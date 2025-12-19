"""
test_t3_policy.py — Unit tests for routing & invariants of T3 policy.

Does not require torch: uses a stub S1 evaluator.
"""

from dataclasses import dataclass

from proof_kernel import FiniteTrace, Halts, Monotone
from t3_policy import T3HaltingPolicy
from s1_kit import S1Eval, Verdict as S1Verdict


@dataclass
class StubS1:
    """
    Deterministic external evaluator:
    - prob = 0.9 if Halts(T) else 0.1
    - confidence = 0.8 always
    """
    bound: int

    def evaluate(self, T: FiniteTrace) -> S1Eval:
        truth = Halts(T)
        prob = 0.9 if truth else 0.1
        logit = 2.1972245773362196 if truth else -2.1972245773362196  # logit(0.9)
        return S1Eval(prob=prob, logit=logit, confidence=0.8, bound=T.bound)

    def decide(self, ev: S1Eval, eps: float = 0.10, threshold: float = 0.5) -> S1Verdict:
        if ev.confidence < eps:
            return S1Verdict.ABSTAIN
        return S1Verdict.HALTS if ev.prob >= threshold else S1Verdict.NOHALT


def mk_trace(bits):
    bt = tuple(bits)
    return FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), len(bt))


def test_routing(bound: int = 10):
    policy = T3HaltingPolicy(s1=StubS1(bound), eps=0.10)

    # monotone all zeros => S2 decides NOHALT
    T0 = mk_trace([False] * bound)
    assert Monotone(T0) and not Halts(T0)
    d0 = policy.decide(T0)
    assert d0.source == "S2"
    assert d0.verdict == "NOHALT"

    # monotone with switchpoint => S2 decides HALTS
    Tm = mk_trace([False] * 3 + [True] * (bound - 3))
    assert Monotone(Tm) and Halts(Tm)
    dm = policy.decide(Tm)
    assert dm.source == "S2"
    assert dm.verdict == "HALTS"

    # non-monotone => S1 used
    Tnm = mk_trace([False, True, False] + [False] * (bound - 3))
    assert not Monotone(Tnm)
    dnm = policy.decide(Tnm)
    assert dnm.source == "S1"
    assert dnm.verdict in ("HALTS", "NOHALT", "ABSTAIN")

    # abstain path when eps too high
    policy2 = T3HaltingPolicy(s1=StubS1(bound), eps=0.99)
    dnm2 = policy2.decide(Tnm)
    assert dnm2.source == "S1"
    assert dnm2.verdict == "ABSTAIN"


if __name__ == "__main__":
    test_routing(10)
    print("PASS")
