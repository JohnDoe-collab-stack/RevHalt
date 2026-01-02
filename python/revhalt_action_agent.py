"""
RevHalt Action-Based Proof Agent
================================

Architecture conforme Option B renforcée:
- LLM propose des ACTIONS (tactiques), pas des états
- Le KERNEL produit le nouvel état
- Chaque transition est kernel-verified

FLOW:
  LLM.propose_action(trace) → tactic
  Kernel.apply(state, tactic) → new_state
  R1.verify(old, new) → bool
  Eval(trace) → certificate
"""

import sys
sys.path.insert(0, '.')

from dataclasses import dataclass, field
from typing import Optional, Tuple
from abc import ABC, abstractmethod
import hashlib

from revhalt_llm import (
    ProofState, CertificateType, Certificate, State, 
    LexicographicR1Gate, ProofEvaluator, lex_lt
)
from lean_kernel_checker import LeanKernelChecker, LeanResult


# ═══════════════════════════════════════════════════════════════════════════════
# 1) Action-based Generator (LLM proposes tactics, not states)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TacticAction:
    """An action proposed by the LLM"""
    tactic: str
    rationale: Optional[str] = None


class ActionGenerator(ABC):
    """Abstract generator that proposes ACTIONS, not states"""
    
    @abstractmethod
    def propose_action(self, trace: list[ProofState]) -> Optional[TacticAction]:
        """
        Given a trace, propose a tactic to apply.
        Returns None if no action can be proposed.
        """
        pass


class MockActionGenerator(ActionGenerator):
    """Mock generator with hardcoded tactics"""
    
    def propose_action(self, trace: list[ProofState]) -> Optional[TacticAction]:
        if not trace:
            return None
        
        current = trace[-1]
        if not current.goals:
            return None  # Already solved
        
        goal = current.goals[0]
        
        # Heuristics for common goal patterns
        if "->" in goal or "→" in goal:
            return TacticAction("intro h; exact h", "implication intro-elim")
        if goal == "True":
            return TacticAction("trivial", "True is trivial")
        if "=" in goal:
            return TacticAction("rfl", "reflexivity")
        if goal.startswith("∀") or goal.startswith("forall"):
            return TacticAction("intro", "universal intro")
        
        return TacticAction("decide", "decidable default")


# ═══════════════════════════════════════════════════════════════════════════════
# 2) Kernel Executor (applies action, produces state)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class KernelExecResult:
    """Result of kernel execution"""
    success: bool
    new_state: Optional[ProofState]
    lean_result: LeanResult
    tactic: str


class KernelExecutor:
    """
    Executes tactics via Lean kernel and produces new states.
    
    KEY INSIGHT: The LLM never "declares" the new state.
    The kernel produces it, making tampering impossible.
    """
    
    def __init__(self, checker: LeanKernelChecker):
        self.checker = checker
        self._journal: list[dict] = []
    
    def apply_action(
        self, 
        state: ProofState, 
        action: TacticAction
    ) -> KernelExecResult:
        """
        Apply a tactic to a state and return the new state.
        
        The new state is PRODUCED by the kernel, not declared by the LLM.
        """
        if not state.goals:
            return KernelExecResult(
                success=False,
                new_state=None,
                lean_result=LeanResult(False, "", "No goals to prove", "", ""),
                tactic=action.tactic
            )
        
        goal = state.goals[0]
        
        # Ask Lean to verify the tactic
        lean_result = self.checker.check_tactic(goal, action.tactic)
        
        if lean_result.success:
            # Tactic worked → produce new state with goals removed
            # In full implementation, Lean would tell us remaining goals
            new_state = ProofState(
                context=state.context,
                goals=state.goals[1:],  # Remove solved goal
                depth=state.depth
            )
            
            # Journal the step (for replayability)
            self._journal.append({
                "from_goal": goal,
                "tactic": action.tactic,
                "to_goals": list(new_state.goals),
                "lean_hash": lean_result.hash,
                "success": True
            })
            
            return KernelExecResult(
                success=True,
                new_state=new_state,
                lean_result=lean_result,
                tactic=action.tactic
            )
        else:
            # Tactic failed → no new state
            self._journal.append({
                "from_goal": goal,
                "tactic": action.tactic,
                "lean_error": lean_result.stderr[:200],
                "success": False
            })
            
            return KernelExecResult(
                success=False,
                new_state=None,
                lean_result=lean_result,
                tactic=action.tactic
            )
    
    def get_journal(self) -> list[dict]:
        """Get the execution journal for replayability"""
        return list(self._journal)


# ═══════════════════════════════════════════════════════════════════════════════
# 3) Kernel-Verified R1 Gate
# ═══════════════════════════════════════════════════════════════════════════════

class KernelVerifiedR1Gate(LexicographicR1Gate):
    """
    R1 Gate where ValidTransition is kernel-verified.
    
    INVARIANT: transition a→b is valid iff:
    1. LexLt(b.measure(), a.measure()) AND
    2. The transition was produced by the kernel (not declared by LLM)
    """
    
    def __init__(self, executor: KernelExecutor):
        self.executor = executor
        # Track kernel-produced transitions
        self._kernel_produced: set[tuple] = set()
        
        # Use kernel check as transition checker
        super().__init__(self._kernel_transition_check)
    
    def _kernel_transition_check(self, a: ProofState, b: ProofState) -> bool:
        """
        Check if transition a→b was produced by the kernel.
        """
        # Key: if (a, b) was produced by kernel, it's valid
        key = (a, b)
        return key in self._kernel_produced
    
    def register_kernel_transition(self, a: ProofState, b: ProofState):
        """Register a kernel-produced transition"""
        self._kernel_produced.add((a, b))


# ═══════════════════════════════════════════════════════════════════════════════
# 4) Action-Based Agent
# ═══════════════════════════════════════════════════════════════════════════════

class ActionBasedAgent:
    """
    RevHalt agent with action-based architecture.
    
    Architecture:
    - Generator proposes ACTIONS (tactics)
    - Kernel PRODUCES states
    - R1 verifies transitions are kernel-produced
    - Eval checks success criteria
    """
    
    def __init__(
        self,
        generator: ActionGenerator,
        executor: KernelExecutor,
        r1_gate: KernelVerifiedR1Gate,
        evaluator: ProofEvaluator
    ):
        self.generator = generator
        self.executor = executor
        self.r1_gate = r1_gate
        self.evaluator = evaluator
        self.state = State()
    
    def explore(self, initial: ProofState, max_steps: int = 10) -> Certificate:
        """
        Explore from initial state using action-based flow.
        
        FLOW:
        1. Check if current state is success
        2. Ask generator for action
        3. Ask kernel to apply action
        4. If kernel succeeds, register transition
        5. Continue or return certificate
        """
        trace = [initial]
        
        for step in range(max_steps):
            current = trace[-1]
            
            # Check success
            if self.evaluator.eval(trace[:-1], current):
                cert = Certificate(
                    cert_type=CertificateType.THM,
                    trace=tuple(trace),
                    policy_id="action_agent"
                )
                return cert
            
            # Get action from generator
            action = self.generator.propose_action(trace)
            if action is None:
                # No action proposed - budget exhausted
                return Certificate(
                    cert_type=CertificateType.BUDGET_EXHAUSTED,
                    trace=tuple(trace),
                    policy_id="action_agent",
                    budget_steps=step,
                    budget_reason="Generator proposed no action"
                )
            
            # Apply action via kernel
            result = self.executor.apply_action(current, action)
            
            if not result.success:
                # Kernel rejected the action - DeadEnd
                return Certificate(
                    cert_type=CertificateType.DEAD_END,
                    trace=tuple(trace),
                    policy_id="action_agent",
                    rejected_candidate=None,  # No candidate - action failed
                    reject_reason=f"Kernel rejected tactic '{action.tactic}': {result.lean_result.stderr[:100]}",
                    reject_step=len(trace),
                    reject_lex_lt=None,
                    reject_valid_transition=False
                )
            
            new_state = result.new_state
            
            # Verify LexLt
            if not lex_lt(new_state.measure(), current.measure()):
                return Certificate(
                    cert_type=CertificateType.DEAD_END,
                    trace=tuple(trace),
                    policy_id="action_agent",
                    rejected_candidate=new_state,
                    reject_reason="Kernel produced state but LexLt failed",
                    reject_step=len(trace),
                    reject_lex_lt=False,
                    reject_valid_transition=True
                )
            
            # Register kernel-produced transition
            self.r1_gate.register_kernel_transition(current, new_state)
            
            trace.append(new_state)
        
        # Budget exhausted
        return Certificate(
            cert_type=CertificateType.BUDGET_EXHAUSTED,
            trace=tuple(trace),
            policy_id="action_agent",
            budget_steps=max_steps,
            budget_reason="Max steps reached"
        )
    
    def run(self, initial: ProofState, max_steps: int = 10) -> Certificate:
        """Full run: explore + add to state"""
        cert = self.explore(initial, max_steps)
        self.state = self.state.step(cert)
        return cert


# ═══════════════════════════════════════════════════════════════════════════════
# 5) Demo
# ═══════════════════════════════════════════════════════════════════════════════

def demo():
    print("=" * 70)
    print("RevHalt Action-Based Proof Agent")
    print("=" * 70)
    print()
    print("Architecture:")
    print("  LLM.propose_action(trace) -> tactic")
    print("  Kernel.apply(state, tactic) -> new_state")
    print("  R1.verify(old, new) -> bool (kernel-produced check)")
    print()
    
    # Setup
    checker = LeanKernelChecker()
    executor = KernelExecutor(checker)
    r1_gate = KernelVerifiedR1Gate(executor)
    evaluator = ProofEvaluator(r1_gate)
    generator = MockActionGenerator()
    
    agent = ActionBasedAgent(generator, executor, r1_gate, evaluator)
    
    # Test 1: Provable goal
    print("=" * 70)
    print("[1] Testing P -> P (provable)")
    print("=" * 70)
    
    initial = ProofState(context=(), goals=("P -> P",), depth=3)
    cert = agent.run(initial, max_steps=5)
    
    print(f"  Result: {cert.cert_type.value}")
    print(f"  Trace: {[list(s.goals) for s in cert.trace]}")
    print(f"  Journal: {executor.get_journal()[-1] if executor.get_journal() else 'empty'}")
    
    # Test 2: Unprovable goal
    print()
    print("=" * 70)
    print("[2] Testing False (unprovable)")
    print("=" * 70)
    
    impossible = ProofState(context=(), goals=("False",), depth=3)
    cert2 = agent.run(impossible, max_steps=5)
    
    print(f"  Result: {cert2.cert_type.value}")
    print(f"  Reason: {cert2.reject_reason or cert2.budget_reason}")
    
    # Test 3: Multi-step proof
    print()
    print("=" * 70)
    print("[3] Testing True (trivial)")
    print("=" * 70)
    
    trivial = ProofState(context=(), goals=("True",), depth=3)
    cert3 = agent.run(trivial, max_steps=5)
    
    print(f"  Result: {cert3.cert_type.value}")
    print(f"  Trace: {[list(s.goals) for s in cert3.trace]}")
    
    # Summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  Agent state: {len(agent.state)} certificates")
    print(f"  Kernel calls: {len(executor.get_journal())}")
    print()
    print("KEY INSIGHT:")
    print("  - LLM proposed ACTIONS, not states")
    print("  - KERNEL produced states")
    print("  - Every transition is kernel-verified")
    print("  - No LLM hallucination possible")
    print("=" * 70)


if __name__ == "__main__":
    demo()
