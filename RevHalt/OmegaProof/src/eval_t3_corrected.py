"""
eval_t3_corrected.py — Metrics for T3 (Corrected)

Since S3 is Total and S1 is Truth, Accuracy = 100% by definition.
The meaningful metrics are:
- S2 Coverage: How much did we internalize?
- S1 Calls: How big is the irreducible frontier?
"""

from itertools import product
from proof_kernel import FiniteTrace, Halts
from t3_policy import T3Policy

def all_traces(bound: int):
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        yield FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)

def evaluate_t3_exhaustive(bound: int = 10):
    policy = T3Policy()
    
    total = 0
    s2_hits = 0
    s1_calls = 0
    
    print(f"--- Evaluating T3 Corrected (Bound={bound}) ---")
    
    for T in all_traces(bound):
        total += 1
        d = policy.decide(T)
        
        # Sanity Check: S3 must agree with Halts(T)/Rev0_K
        truth = Halts(T)
        pred = (d.verdict == "HALTS")
        
        if pred != truth:
            raise RuntimeError(f"FATAL: S3 (Total) disagrees with Truth! Trace: {T}, Decision: {d}")
        
        if d.source == "S2":
            s2_hits += 1
        elif d.source == "S1":
            s1_calls += 1
        else:
            raise RuntimeError(f"Unknown Source: {d.source}")

    coverage = s2_hits / total
    frontier = s1_calls / total
    
    print(f"Total Traces: {total}")
    print(f"S2 Decided (Internalized): {s2_hits} ({coverage:.2%})")
    print(f"S1 Called  (Frontier):     {s1_calls} ({frontier:.2%})")
    print("Accuracy: 100.00% (Verified)")
    
    return {"total": total, "s2": s2_hits, "s1": s1_calls}

if __name__ == "__main__":
    evaluate_t3_exhaustive(10)
