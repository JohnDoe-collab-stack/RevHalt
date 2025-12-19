"""
eval_t3.py — Exact evaluation for T3 policy (finite exhaustive)

Focus: metrics on *decided* outputs (selective classification) + coverage,
and breakdown by provenance (S2 vs S1).

This avoids Monte Carlo artefacts in tiny-negative settings.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Dict, List, Tuple

from proof_kernel import FiniteTrace, Halts, Monotone
from t3_policy import T3HaltingPolicy


def all_traces(bound: int):
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        yield FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)


@dataclass(frozen=True)
class ExactPolicyMetrics:
    bound: int
    total: int
    decided: int
    abstained: int
    coverage: float

    tp: int
    tn: int
    fp: int
    fn: int

    accuracy_decided: float
    tpr: float
    tnr: float

    source_counts: Dict[str, int]


def exact_metrics_policy(policy: T3HaltingPolicy, bound: int) -> ExactPolicyMetrics:
    total = 0
    decided = 0
    abstained = 0
    tp = tn = fp = fn = 0
    source_counts: Dict[str, int] = {}

    for T in all_traces(bound):
        total += 1
        truth = Halts(T)
        d = policy.decide(T)
        source_counts[d.source] = source_counts.get(d.source, 0) + 1

        if d.verdict not in ("HALTS", "NOHALT"):
            abstained += 1
            continue

        decided += 1
        pred = (d.verdict == "HALTS")
        if pred and truth:
            tp += 1
        elif (not pred) and (not truth):
            tn += 1
        elif pred and (not truth):
            fp += 1
        else:
            fn += 1

    accuracy = (tp + tn) / decided if decided else 0.0
    tpr = tp / (tp + fn) if (tp + fn) else 0.0
    tnr = tn / (tn + fp) if (tn + fp) else 0.0
    coverage = decided / total if total else 0.0

    return ExactPolicyMetrics(
        bound=bound,
        total=total,
        decided=decided,
        abstained=abstained,
        coverage=coverage,
        tp=tp,
        tn=tn,
        fp=fp,
        fn=fn,
        accuracy_decided=accuracy,
        tpr=tpr,
        tnr=tnr,
        source_counts=source_counts,
    )


def monotone_failure_cases(policy: T3HaltingPolicy, bound: int) -> List[Tuple[Tuple[bool, ...], str, bool]]:
    """
    Returns list of (trace_bits, verdict, truth) for monotone traces where the policy
    gives a *decided* verdict that is incorrect, or abstains/unknown.
    For T3, expected to be empty: monotone traces must be decided correctly by S2.
    """
    failures = []
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        T = FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)
        if not Monotone(T):
            continue
        truth = Halts(T)
        d = policy.decide(T)
        if d.verdict not in ("HALTS", "NOHALT"):
            failures.append((bt, d.verdict, truth))
        else:
            pred = (d.verdict == "HALTS")
            if pred != truth:
                failures.append((bt, d.verdict, truth))
    return failures
