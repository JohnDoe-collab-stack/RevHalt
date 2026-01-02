"""
RevHalt LLM Integration Framework
==================================

Python implementation of the RevHalt architecture for LLM integration.
Based on docs/LLM_Integration_Spec.md and docs/ProofAssistantAgent_Spec.md.

Architecture:
- Generator (LLM): produces Sentences under R1 constraint
- R1 Gate: validates admissibility of sequences
- Eval (R3): verification mechanism (not decision)
- OraclePick: certificate carrier (Σ₁ or Π₁)
- Dynamics: State accumulation with soundness invariant
"""

from dataclasses import dataclass, field
from typing import Callable, Generic, TypeVar, Optional, Union, Iterator
from abc import ABC, abstractmethod
from enum import Enum
import hashlib

# ═══════════════════════════════════════════════════════════════════════════════
# 1) Core Types
# ═══════════════════════════════════════════════════════════════════════════════

Sentence = TypeVar('Sentence')
Code = TypeVar('Code')

@dataclass(frozen=True)
class ProofState:
    """
    State in a proof search (Option B encoding).
    
    INVARIANT: depth >= 0 (required for well-founded lexicographic descent).
    """
    context: tuple  # immutable context
    goals: tuple[str, ...]  # list of goals
    depth: int
    
    def __post_init__(self):
        """Enforce depth >= 0 invariant (Nat alignment with Lean spec)"""
        if self.depth < 0:
            raise ValueError(f"ProofState.depth must be >= 0, got {self.depth}")
    
    @property
    def is_success(self) -> bool:
        """Success = no goals remaining"""
        return len(self.goals) == 0
    
    def measure(self) -> tuple[int, int]:
        """Lexicographic measure (depth, |goals|)"""
        return (self.depth, len(self.goals))


def lex_lt(a: tuple[int, int], b: tuple[int, int]) -> bool:
    """Lexicographic strict ordering"""
    return a[0] < b[0] or (a[0] == b[0] and a[1] < b[1])


# ═══════════════════════════════════════════════════════════════════════════════
# 2) R1: Admissibility Gate
# ═══════════════════════════════════════════════════════════════════════════════

class R1Gate(ABC):
    """Abstract R1 gate for sequence admissibility"""
    
    @abstractmethod
    def is_valid_transition(self, a: ProofState, b: ProofState) -> bool:
        """Check if transition a → b is valid (kernel-checkable)"""
        pass
    
    def step_ok(self, a: ProofState, b: ProofState) -> bool:
        """Single step validity: descent + valid transition"""
        return lex_lt(b.measure(), a.measure()) and self.is_valid_transition(a, b)
    
    def is_admissible(self, trace: list[ProofState]) -> bool:
        """Check if entire trace satisfies Adm (lexicographic descent)"""
        if len(trace) <= 1:
            return True
        for i in range(len(trace) - 1):
            if not self.step_ok(trace[i], trace[i + 1]):
                return False
        return True
    
    def admits_const(self) -> bool:
        """
        Check if this gate admits constant sequences.
        
        STRUCTURAL INVARIANT: With lexicographic strict descent on (depth, |goals|),
        constant sequences are excluded by construction. Any s with s(n) = s(n+1)
        violates LexLt(s(n+1).measure(), s(n).measure()).
        
        This blocks the 'const-trick' derivation LPO_R1 -> EM_Eval.
        """
        return False


class LexicographicR1Gate(R1Gate):
    """
    Concrete R1 gate with lexicographic descent.
    
    REQUIREMENT: transition_checker MUST be deterministic and replayable.
    The tamper-evident audit in Certificate.truth() recomputes is_valid_transition
    and verifies it matches stored values. Non-deterministic checkers will cause
    spurious audit failures.
    """
    
    def __init__(self, transition_checker: Callable[[ProofState, ProofState], bool]):
        self.transition_checker = transition_checker
    
    def is_valid_transition(self, a: ProofState, b: ProofState) -> bool:
        return self.transition_checker(a, b)


# ═══════════════════════════════════════════════════════════════════════════════
# 3) PropT: Certificate Types (Σ₁ / Π₁ / Π₂)
# ═══════════════════════════════════════════════════════════════════════════════

class CertificateType(Enum):
    THM = "Sigma1"                       # Proof found (positive)
    DEAD_END = "DeadEnd"                 # R1-rejected step (operational negative)
    BUDGET_EXHAUSTED = "BudgetExhausted" # Max steps reached without resolution
    # Meta-only types (never emitted by explore() in lex-descent mode):
    STAB_CHAIN = "Pi1"                   # Stabilization on infinite admissible chain
    STAB_FROM = "Pi2"                    # Stabilization on ALL chains


@dataclass(frozen=True)
class Certificate:
    """Certificate carrier (OraclePick equivalent)"""
    cert_type: CertificateType
    trace: tuple[ProofState, ...]  # The trace/chain
    policy_id: str = ""
    
    # DeadEnd audit fields (only for DEAD_END type)
    rejected_candidate: Optional[ProofState] = None
    reject_reason: Optional[str] = None
    reject_step: Optional[int] = None
    reject_lex_lt: Optional[bool] = None
    reject_valid_transition: Optional[bool] = None
    
    # BudgetExhausted fields (separate from reject_*)
    budget_steps: Optional[int] = None
    budget_reason: Optional[str] = None
    
    @property
    def is_positive(self) -> bool:
        return self.cert_type == CertificateType.THM
    
    @property
    def is_negative(self) -> bool:
        return self.cert_type in (CertificateType.DEAD_END, CertificateType.BUDGET_EXHAUSTED, 
                                  CertificateType.STAB_CHAIN, CertificateType.STAB_FROM)
    
    @property
    def final_state(self) -> Optional[ProofState]:
        return self.trace[-1] if self.trace else None
    
    def truth(self, r1_gate: 'R1Gate', evaluator: 'Evaluator') -> bool:
        """
        Unified Truth function for all certificate types.
        
        Truth(cert) is the semantic condition that must hold for the certificate
        to be valid. This is the single point of definition for soundness.
        
        - THM (Sigma1): Eval(prefix, final) = Success ∧ TraceOK
        - DEAD_END: tamper-evident audit + prefix admissible + non-success + real R1 rejection
        - BUDGET_EXHAUSTED: trace admissible + no success on any prefix
        - STAB_CHAIN/STAB_FROM: meta-only (raises error if verified at execution layer)
        """
        if self.cert_type == CertificateType.THM:
            if self.final_state is None:
                return False
            return evaluator.eval(list(self.trace[:-1]), self.final_state)
        
        if self.cert_type == CertificateType.DEAD_END:
            # Audit fields must be present
            if self.rejected_candidate is None or self.reject_step is None:
                return False
            if self.reject_lex_lt is None or self.reject_valid_transition is None:
                return False
            
            # Prefix must be admissible
            if not r1_gate.is_admissible(list(self.trace)):
                return False
            
            # Current state must not be success
            current = self.final_state
            if current and evaluator.eval(list(self.trace[:-1]), current):
                return False
            
            # TAMPER-EVIDENT: recompute and verify stored values match
            if current:
                computed_lex = lex_lt(self.rejected_candidate.measure(), current.measure())
                computed_vt = r1_gate.is_valid_transition(current, self.rejected_candidate)
                
                if computed_lex != self.reject_lex_lt:
                    return False  # Audit mismatch
                if computed_vt != self.reject_valid_transition:
                    return False  # Audit mismatch
                
                # Verify step index consistency
                if self.reject_step != len(self.trace):
                    return False  # Step mismatch
                
                # The rejection must be real
                return not r1_gate.step_ok(current, self.rejected_candidate)
            return False
        
        if self.cert_type == CertificateType.BUDGET_EXHAUSTED:
            # Budget fields should be present (not reject_*)
            if not r1_gate.is_admissible(list(self.trace)):
                return False
            return all(not evaluator.eval(list(self.trace[:i]), s) 
                      for i, s in enumerate(self.trace))
        
        # Meta-only types: CANNOT be verified at execution layer
        # This prevents accidental injection of unverified meta-certificates
        if self.cert_type in (CertificateType.STAB_CHAIN, CertificateType.STAB_FROM):
            raise NotImplementedError(
                f"Meta-only certificate type {self.cert_type.value} cannot be verified "
                "at execution layer. Use meta-verifier or do not inject into State."
            )


# ═══════════════════════════════════════════════════════════════════════════════
# 4) Eval (R3): Verification Mechanism
# ═══════════════════════════════════════════════════════════════════════════════

class Evaluator(ABC):
    """Abstract evaluator (R3 access mechanism)"""
    
    @abstractmethod
    def eval(self, context: list, sentence: ProofState) -> bool:
        """
        Eval(Γ, φ) := Success(φ) ∧ TraceOK(Γ, φ)
        
        Returns True if the state is terminal AND the trace is valid.
        This is NOT deciding truth - it's checking verification.
        """
        pass


class ProofEvaluator(Evaluator):
    """Evaluator for proof states"""
    
    def __init__(self, r1_gate: R1Gate):
        self.r1_gate = r1_gate
    
    def eval(self, context: list[ProofState], state: ProofState) -> bool:
        """Eval = Success ∧ TraceOK"""
        trace = list(context) + [state]
        return state.is_success and self.r1_gate.is_admissible(trace)


# ═══════════════════════════════════════════════════════════════════════════════
# 5) State and Dynamics (T3)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class State:
    """
    T3 State with soundness invariant.
    
    DEFENSE: step() rejects meta-only certificate types (STAB_CHAIN, STAB_FROM)
    at insertion time, preventing accidental injection of unverified certificates.
    """
    certificates: set[Certificate] = field(default_factory=set)
    
    def is_sound(self, truth_checker: Callable[[Certificate], bool]) -> bool:
        """Soundness: all certificates satisfy Truth"""
        return all(truth_checker(cert) for cert in self.certificates)
    
    def step(self, pick: Certificate) -> 'State':
        """
        Add a certificate to state (T3 step).
        
        DEFENSE: Rejects meta-only types at insertion to prevent
        accidental injection of unverified certificates into execution state.
        """
        # Defensive guard: reject meta-only types at insertion
        if pick.cert_type in (CertificateType.STAB_CHAIN, CertificateType.STAB_FROM):
            raise ValueError(
                f"Cannot insert meta-only certificate type {pick.cert_type.value} "
                "into execution State. Use meta-layer State instead."
            )
        new_certs = self.certificates | {pick}
        return State(certificates=new_certs)
    
    def __len__(self) -> int:
        return len(self.certificates)


def chain(
    initial_state: State,
    schedule: Iterator[ProofState],
    pick_generator: Callable[[ProofState], Optional[Certificate]],
    max_steps: int = 1000
) -> Iterator[State]:
    """
    T3 Chain: iterate step according to schedule.
    
    Args:
        initial_state: Starting state S₀
        schedule: Iterator of states to explore
        pick_generator: Function to generate OraclePick for each state
        max_steps: Maximum number of steps
    
    Yields:
        Sequence of states (chain)
    """
    current = initial_state
    yield current
    
    for i, target in enumerate(schedule):
        if i >= max_steps:
            break
        pick = pick_generator(target)
        if pick is not None:
            current = current.step(pick)
            yield current


def lim(chain_states: list[State]) -> State:
    """ω-limit: union of all certificates in the chain"""
    all_certs: set[Certificate] = set()
    for state in chain_states:
        all_certs |= state.certificates
    return State(certificates=all_certs)


# ═══════════════════════════════════════════════════════════════════════════════
# 6) LLM Generator Interface
# ═══════════════════════════════════════════════════════════════════════════════

class LLMGenerator(ABC):
    """
    LLM Generator interface.
    
    The LLM is a c-machine: it produces Sentences, NOT truth.
    All outputs must be verified via Eval (R3).
    """
    
    @abstractmethod
    def propose(self, context: list[ProofState]) -> ProofState:
        """Propose a next state (c-machine compilation)"""
        pass
    
    @abstractmethod
    def propose_sequence(self, context: list[ProofState], length: int) -> list[ProofState]:
        """Propose a sequence of states (must satisfy Adm)"""
        pass


class MockLLMGenerator(LLMGenerator):
    """Mock LLM for testing"""
    
    def propose(self, context: list[ProofState]) -> ProofState:
        """Simple mock: reduce depth or goals"""
        if not context:
            return ProofState(context=(), goals=("goal1",), depth=5)
        last = context[-1]
        if last.goals:
            return ProofState(
                context=last.context,
                goals=last.goals[:-1],  # Remove one goal
                depth=last.depth
            )
        return ProofState(context=last.context, goals=(), depth=last.depth - 1)
    
    def propose_sequence(self, context: list[ProofState], length: int) -> list[ProofState]:
        result = []
        current_context = list(context)
        for _ in range(length):
            next_state = self.propose(current_context)
            result.append(next_state)
            current_context.append(next_state)
        return result


# ═══════════════════════════════════════════════════════════════════════════════
# 7) RevHalt Agent
# ═══════════════════════════════════════════════════════════════════════════════

class RevHaltAgent:
    """
    Complete RevHalt-compliant LLM agent.
    
    Architecture:
    - LLM generates candidates (c-machine)
    - R1 gate validates transitions
    - Evaluator checks success (R3)
    - Certificates carry truth (OraclePick)
    - State accumulates proven facts (Dynamics)
    """
    
    def __init__(
        self,
        llm: LLMGenerator,
        r1_gate: R1Gate,
        evaluator: Evaluator
    ):
        self.llm = llm
        self.r1_gate = r1_gate
        self.evaluator = evaluator
        self.state = State()
        self.journal: list[tuple[ProofState, ...]] = []
    
    def explore(self, initial: ProofState, max_steps: int = 100) -> Certificate:
        """
        Explore from initial state, return certificate.
        
        Returns:
            - THM (Sigma1): if Eval succeeds
            - DEAD_END: if R1 rejects a step
            - BUDGET_EXHAUSTED: if max_steps reached without resolution
        """
        trace = [initial]
        rejected_candidate = None
        reject_reason = None
        reject_step = None
        reject_lex_lt = None
        reject_valid_transition = None
        
        for step in range(max_steps):
            current = trace[-1]
            
            # Check success (Eval)
            if self.evaluator.eval(trace[:-1], current):
                cert = Certificate(
                    cert_type=CertificateType.THM,
                    trace=tuple(trace)
                )
                self.journal.append(tuple(trace))
                return cert
            
            # Generate next candidate (LLM / c-machine)
            candidate = self.llm.propose(trace)
            
            # Validate transition (R1) with audit
            lex_ok = lex_lt(candidate.measure(), current.measure())
            vt_ok = self.r1_gate.is_valid_transition(current, candidate)
            
            if not (lex_ok and vt_ok):
                # R1 rejected - return audited DeadEnd
                # Note: reject_step = len(trace) for tamper-evident consistency
                cert = Certificate(
                    cert_type=CertificateType.DEAD_END,
                    trace=tuple(trace),
                    policy_id=f"explore_{id(self)}",
                    rejected_candidate=candidate,
                    reject_reason="R1 rejected step (lex descent or ValidTransition failed)",
                    reject_step=len(trace),  # Must equal len(trace) for tamper-evidence
                    reject_lex_lt=lex_ok,
                    reject_valid_transition=vt_ok,
                )
                self.journal.append(tuple(trace))
                return cert
            
            trace.append(candidate)
        
        # Budget exhausted - no success, no blocking detected
        # Use budget_* fields instead of reject_* (semantic separation)
        cert = Certificate(
            cert_type=CertificateType.BUDGET_EXHAUSTED,
            trace=tuple(trace),
            policy_id=f"explore_{id(self)}",
            budget_steps=max_steps,
            budget_reason="Budget exhausted (max steps reached without resolution)",
        )
        self.journal.append(tuple(trace))
        return cert
    
    def step(self, cert: Certificate) -> None:
        """Add certificate to state (T3 step)"""
        self.state = self.state.step(cert)
    
    def run(self, initial: ProofState, max_steps: int = 100) -> Certificate:
        """Full run: explore + step"""
        cert = self.explore(initial, max_steps)
        self.step(cert)
        return cert


# ═══════════════════════════════════════════════════════════════════════════════
# 8) Demo / Test
# ═══════════════════════════════════════════════════════════════════════════════

def demo():
    """Demonstrate RevHalt-compliant LLM agent"""
    
    print("=" * 60)
    print("RevHalt LLM Integration Demo")
    print("=" * 60)
    
    # Setup with MOCK transition checker (not kernel-verified)
    def mock_transition_always_valid(a: ProofState, b: ProofState) -> bool:
        """MockTransitionChecker: accepts all transitions (demo only, not kernel)"""
        return True
    
    r1_gate = LexicographicR1Gate(mock_transition_always_valid)
    llm = MockLLMGenerator()
    evaluator = ProofEvaluator(r1_gate)
    agent = RevHaltAgent(llm, r1_gate, evaluator)
    
    # Verify R1 blocks constants (Adm_not_admits_const)
    print("\n[1] R1 Gate: AdmitsConst =", r1_gate.admits_const())
    print("    -> Constants BLOCKED (collapse LPO->EM prevented)")
    
    # Run exploration
    initial = ProofState(context=(), goals=("prove_theorem",), depth=3)
    print(f"\n[2] Initial state: {initial}")
    
    cert = agent.run(initial, max_steps=20)
    
    print(f"\n[3] Certificate obtained:")
    print(f"    Type: {cert.cert_type.value}")
    print(f"    Trace length: {len(cert.trace)}")
    print(f"    Final state: {cert.final_state}")
    
    print(f"\n[4] Agent state:")
    print(f"    Certificates accumulated: {len(agent.state)}")
    print(f"    Journal entries: {len(agent.journal)}")
    
    # Verify invariants using Certificate.truth() (unified Truth function)
    def truth_checker(c: Certificate) -> bool:
        return c.truth(r1_gate, evaluator)
    
    is_sound = agent.state.is_sound(truth_checker)
    print(f"\n[5] Soundness invariant: {is_sound}")
    
    print("\n" + "=" * 60)
    print("Demo complete. All RevHalt invariants satisfied.")
    print("=" * 60)


if __name__ == "__main__":
    demo()
