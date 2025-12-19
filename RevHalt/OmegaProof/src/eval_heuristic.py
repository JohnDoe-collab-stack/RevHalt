"""
eval_heuristic.py — Evaluating the Coverage Gain

Compare:
1. Pure S2 (Monotone)
2. S2 + ML (Witness Search)
3. S1 (Fallback)

Goal: Maximize S2+ML, Minimize S1.
"""

import torch
from itertools import product
from proof_kernel import FiniteTrace
from s2_extended import S2ExtendedProver
from ml_witness import WitnessModel
from s2_heuristic import S2Heuristic
from s1_oracle import S1Oracle
from t3_types import Verdict

def all_traces(bound: int):
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        yield FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)

def eval_heuristic_gain(bound=10, model_path="witness_model.pt"):
    # Load Model
    model = WitnessModel(bound)
    try:
        state = torch.load(model_path)
        model.load_state_dict(state)
        print("Loaded trained model.")
    except:
        print("Warning: Using untrained model (random weights).")

    # Components
    base_s2 = S2ExtendedProver()
    heuristic_s2 = S2Heuristic(base_s2, model, k=3)
    oracle_s1 = S1Oracle()

    # Stats
    total = 0
    s2_base_hits = 0
    s2_ml_hits = 0
    s1_calls = 0

    print(f"\nEvaluating S2 Coverage (Bound={bound})...")

    for T in all_traces(bound):
        total += 1
        
        # 1. Try Heuristic S2 (which includes Base S2)
        d = heuristic_s2.decide(T)
        
        if d.verdict != Verdict.UNKNOWN:
            # It was decided internally!
            if d.source == "S2":
                s2_base_hits += 1
            elif d.source == "S2+ML":
                s2_ml_hits += 1
        else:
            # Fallback to Oracle
            s1_calls += 1

    coverage_base = s2_base_hits / total
    coverage_total = (s2_base_hits + s2_ml_hits) / total
    frontier = s1_calls / total

    print(f"Total Traces: {total}")
    print(f"S2 Base (Monotone):     {s2_base_hits} ({coverage_base:.2%})")
    print(f"S2 + ML (Witness):      {s2_base_hits + s2_ml_hits} ({coverage_total:.2%})")
    print(f"  > Gain from ML:       +{s2_ml_hits}")
    print(f"S1 Frontier (Residual): {s1_calls} ({frontier:.2%})")

if __name__ == "__main__":
    eval_heuristic_gain()
