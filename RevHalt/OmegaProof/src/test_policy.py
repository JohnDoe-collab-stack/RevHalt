"""
Unit tests for HaltingPolicy invariants.

These tests do NOT depend on a trained checkpoint.
They use a deterministic dummy model with controlled probabilities.
"""

from __future__ import annotations

from itertools import product

from proof_kernel import FiniteTrace, Halts, Monotone
from ml_policy import HaltingPolicy, compute_coverage_curve

try:
    import torch
    import torch.nn as nn
except Exception:
    torch = None
    nn = None


class DummySafeModel(nn.Module):
    """
    Deterministic model:
      - outputs p=0.0 for all-zeros trace
      - outputs p=1.0 for any trace with at least one 1
    This matches Halts exactly in the finite bit-trace sense.
    """
    def forward(self, x):
        s = x.sum(dim=1, keepdim=True)
        return (s > 0.0).float()  # probability already in [0,1]


def _trace_from_bits(bits):
    bt = tuple(bits)
    bound = len(bt)
    return FiniteTrace(lambda n, bt=bt: bt[n], bound)


def test_null_trace_is_nohalt():
    if torch is None:
        return

    bound = 10
    model = DummySafeModel()
    policy = HaltingPolicy(model=model, bound=bound, eps=0.10)

    zeros = [False] * bound
    decision, p = policy.decide(zeros)

    assert decision == "NOHALT"
    assert p == 0.0


def test_monotone_switchpoints_never_misclassified_when_decided():
    if torch is None:
        return

    bound = 10
    model = DummySafeModel()
    policy = HaltingPolicy(model=model, bound=bound, eps=0.10)

    for sp in range(bound + 1):
        bits = [False] * sp + [True] * (bound - sp)
        T = _trace_from_bits(bits)
        assert Monotone(T)

        truth = bool(Halts(T))
        decision, _p = policy.decide(T)

        # DummySafeModel never abstains; but this test allows abstention in general
        if decision == "ABSTAIN":
            continue
        pred = (decision == "HALTS")
        assert pred == truth


def test_coverage_curve_reproducible():
    if torch is None:
        return

    bound = 8  # keep test fast
    model = DummySafeModel()
    policy = HaltingPolicy(model=model, bound=bound, eps=0.10)

    curve1 = compute_coverage_curve(policy)
    curve2 = compute_coverage_curve(policy)

    assert curve1 == curve2


if __name__ == "__main__":
    test_null_trace_is_nohalt()
    test_monotone_switchpoints_never_misclassified_when_decided()
    test_coverage_curve_reproducible()
    print("PASS")
