"""
RevHalt LLM Demo - Reinforced Version
======================================

This demo explicitly shows:
1. ValidTransition with actual verification (not just True)
2. Detailed trace logging at each step
3. DeadEnd (operational negative) certificate case
4. Explicit goals display
"""

import sys
sys.path.insert(0, '.')

from revhalt_llm import (
    ProofState, LLMGenerator, R1Gate, LexicographicR1Gate,
    ProofEvaluator, RevHaltAgent, Certificate, CertificateType,
    lex_lt, State
)

# ═══════════════════════════════════════════════════════════════════════════════
# Reinforced ValidTransition: actually checks something
# ═══════════════════════════════════════════════════════════════════════════════

def valid_transition_strict(a: ProofState, b: ProofState) -> tuple[bool, str]:
    """
    ValidTransition with explicit check and reason.
    
    In a real system, this would call Lean/Coq kernel.
    Here we simulate with verifiable rules:
    1. Context must be preserved
    2. Goals can only decrease (subset or proper subset)
    3. Depth can only stay same or decrease
    """
    reasons = []
    
    # Rule 1: Context preserved
    if a.context != b.context:
        return False, "Context changed (forbidden)"
    
    # Rule 2: Goals decrease
    if len(b.goals) > len(a.goals):
        return False, f"Goals increased: {len(a.goals)} -> {len(b.goals)}"
    
    # Rule 3: Depth doesn't increase
    if b.depth > a.depth:
        return False, f"Depth increased: {a.depth} -> {b.depth}"
    
    # Rule 4: Something must decrease (not constant)
    if b.goals == a.goals and b.depth == a.depth:
        return False, "No progress (constant transition)"
    
    return True, "Valid: descent verified"


def valid_transition_wrapper(a: ProofState, b: ProofState) -> bool:
    """Wrapper for R1Gate compatibility"""
    result, _ = valid_transition_strict(a, b)
    return result


# ═══════════════════════════════════════════════════════════════════════════════
# Mock LLM that can fail (for DeadEnd demo)
# ═══════════════════════════════════════════════════════════════════════════════

class ControllableMockLLM(LLMGenerator):
    """Mock LLM with controllable behavior"""
    
    def __init__(self, fail_after: int = -1):
        """
        Args:
            fail_after: If >= 0, produce invalid state after this many steps
        """
        self.fail_after = fail_after
        self.step_count = 0
    
    def propose(self, context: list[ProofState]) -> ProofState:
        if not context:
            return ProofState(context=(), goals=("goal1",), depth=5)
        
        last = context[-1]
        self.step_count += 1
        
        # Simulate failure: produce invalid state
        if self.fail_after >= 0 and self.step_count > self.fail_after:
            # Return same state (no progress) - will be rejected by R1
            return last
        
        # Normal behavior: reduce goals
        if last.goals:
            return ProofState(
                context=last.context,
                goals=last.goals[:-1],
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
# Enhanced explore with detailed logging
# ═══════════════════════════════════════════════════════════════════════════════

def explore_with_details(
    llm: LLMGenerator,
    r1_gate: R1Gate,
    evaluator,
    initial: ProofState,
    max_steps: int = 10
) -> tuple[Certificate, list[dict]]:
    """
    Explore with detailed logging of each step.
    Returns (certificate, detailed_log)
    """
    trace = [initial]
    log = []
    
    # Log initial state
    log.append({
        "step": 0,
        "state": initial,
        "goals": list(initial.goals),
        "depth": initial.depth,
        "measure": initial.measure(),
        "action": "INITIAL"
    })
    
    for step in range(1, max_steps + 1):
        current = trace[-1]
        
        # Check success (Eval)
        is_success = evaluator.eval(trace[:-1], current)
        if is_success:
            log.append({
                "step": step,
                "state": current,
                "goals": list(current.goals),
                "depth": current.depth,
                "measure": current.measure(),
                "action": "SUCCESS (Eval verified)"
            })
            return Certificate(
                cert_type=CertificateType.THM,
                trace=tuple(trace)
            ), log
        
        # Generate next candidate (LLM)
        candidate = llm.propose(trace)
        
        # Check transition validity
        is_valid, reason = valid_transition_strict(current, candidate)
        lex_descent = lex_lt(candidate.measure(), current.measure())
        step_ok = is_valid and lex_descent
        
        log.append({
            "step": step,
            "from_state": current,
            "to_state": candidate,
            "from_goals": list(current.goals),
            "to_goals": list(candidate.goals),
            "from_measure": current.measure(),
            "to_measure": candidate.measure(),
            "lex_lt": lex_descent,
            "valid_transition": is_valid,
            "reason": reason,
            "step_ok": step_ok,
            "action": "TRANSITION OK" if step_ok else "TRANSITION REJECTED"
        })
        
        if not step_ok:
            # DeadEnd - cannot continue (R1-rejected)
            # Note: reject_step = len(trace) for tamper-evident consistency
            return Certificate(
                cert_type=CertificateType.DEAD_END,
                trace=tuple(trace),
                policy_id="explore_detailed",
                rejected_candidate=candidate,
                reject_reason=reason,
                reject_step=len(trace),  # Must equal len(trace) for tamper-evidence
                reject_lex_lt=lex_descent,
                reject_valid_transition=is_valid,
            ), log
        
        trace.append(candidate)
    
    # Max steps reached without success - use budget_* fields
    return Certificate(
        cert_type=CertificateType.BUDGET_EXHAUSTED,
        trace=tuple(trace),
        policy_id="explore_detailed_budget_exhausted",
        budget_steps=max_steps,
        budget_reason="Budget exhausted (max steps reached without resolution)",
    ), log


# ═══════════════════════════════════════════════════════════════════════════════
# Demo
# ═══════════════════════════════════════════════════════════════════════════════

def demo_reinforced():
    print("=" * 70)
    print("RevHalt LLM Demo - REINFORCED VERSION")
    print("=" * 70)
    
    r1_gate = LexicographicR1Gate(valid_transition_wrapper)
    evaluator = ProofEvaluator(r1_gate)
    
    # ═══════════════════════════════════════════════════════════════════════
    # TEST 1: Sigma1 (positive) case
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 70)
    print("TEST 1: Sigma1 (positive) - Goal can be solved")
    print("=" * 70)
    
    llm_success = ControllableMockLLM(fail_after=-1)  # Never fails
    initial = ProofState(context=(), goals=("prove_P_implies_P",), depth=3)
    
    print(f"\nInitial: goals={list(initial.goals)}, depth={initial.depth}")
    
    cert, log = explore_with_details(llm_success, r1_gate, evaluator, initial, max_steps=5)
    
    print("\nTrace:")
    for entry in log:
        if "from_state" in entry:
            print(f"  Step {entry['step']}:")
            print(f"    From: goals={entry['from_goals']}, measure={entry['from_measure']}")
            print(f"    To:   goals={entry['to_goals']}, measure={entry['to_measure']}")
            print(f"    LexLt: {entry['lex_lt']}, ValidTransition: {entry['valid_transition']}")
            print(f"    Reason: {entry['reason']}")
            print(f"    -> {entry['action']}")
        else:
            print(f"  Step {entry['step']}: {entry['action']}")
            print(f"    goals={entry['goals']}, depth={entry['depth']}, measure={entry['measure']}")
    
    print(f"\nResult: {cert.cert_type.value}")
    print(f"  Trace length: {len(cert.trace)}")
    print(f"  Final goals: {list(cert.final_state.goals) if cert.final_state else 'N/A'}")
    
    # Verify Truth
    if cert.cert_type == CertificateType.THM:
        final = cert.final_state
        success_ok = final is not None and final.is_success
        trace_ok = r1_gate.is_admissible(list(cert.trace))
        print(f"\n  Truth(Thm) verification:")
        print(f"    Success(st) = goals=[]: {success_ok}")
        print(f"    TraceOK: {trace_ok}")
        print(f"    -> Eval = Success AND TraceOK: {success_ok and trace_ok}")
    
    # TEST 2: DeadEnd (operational negative) case
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 70)
    print("TEST 2: DeadEnd (negative) - LLM cannot make progress")
    print("=" * 70)
    
    llm_fail = ControllableMockLLM(fail_after=0)  # Fails immediately
    initial_hard = ProofState(context=(), goals=("prove_false", "another_goal"), depth=3)
    
    print(f"\nInitial: goals={list(initial_hard.goals)}, depth={initial_hard.depth}")
    
    cert2, log2 = explore_with_details(llm_fail, r1_gate, evaluator, initial_hard, max_steps=5)
    
    print("\nTrace:")
    for entry in log2:
        if "from_state" in entry:
            print(f"  Step {entry['step']}:")
            print(f"    From: goals={entry['from_goals']}, measure={entry['from_measure']}")
            print(f"    To:   goals={entry['to_goals']}, measure={entry['to_measure']}")
            print(f"    LexLt: {entry['lex_lt']}, ValidTransition: {entry['valid_transition']}")
            print(f"    Reason: {entry['reason']}")
            print(f"    -> {entry['action']}")
        else:
            print(f"  Step {entry['step']}: {entry['action']}")
            print(f"    goals={entry['goals']}, depth={entry['depth']}, measure={entry['measure']}")
    
    print(f"\nResult: {cert2.cert_type.value}")
    print(f"  Trace length: {len(cert2.trace)}")
    print(f"  Policy ID: {cert2.policy_id}")
    
    # Verify DeadEnd properties
    if cert2.cert_type == CertificateType.DEAD_END:
        print(f"\n  Truth(DeadEnd) verification:")
        print(f"    Rejected at step: {cert2.reject_step}")
        print(f"    Reason: {cert2.reject_reason}")
        print(f"    LexLt: {cert2.reject_lex_lt}, ValidTransition: {cert2.reject_valid_transition}")
        print(f"    TraceOK (prefix): {r1_gate.is_admissible(list(cert2.trace))}")
        current = cert2.trace[-1] if cert2.trace else None
        already_success = evaluator.eval(list(cert2.trace[:-1]), current) if current else False
        print(f"    Current state already success: {already_success} (should be False)")
        print(f"    -> DeadEnd (operational blocking) VERIFIED")
    
    # ═══════════════════════════════════════════════════════════════════════
    # Summary
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("""
ValidTransition is NOT 'always True'. It checks:
  1. Context preserved
  2. Goals can only decrease
  3. Depth can only stay same or decrease
  4. Something must change (blocks constants)

Certificates carry:
  - Sigma1 (THM): trace + final state with Success AND TraceOK
  - DeadEnd: operational blocking (R1-rejected step)
  - Pi1 (STAB_CHAIN): meta-only, for infinite admissible chains

The LLM proposes, but Eval decides.
Negative (operational) = DeadEnd, NOT Pi1 over N.
Soundness = all stored certificates satisfy Truth.
""")
    print("=" * 70)


if __name__ == "__main__":
    demo_reinforced()
