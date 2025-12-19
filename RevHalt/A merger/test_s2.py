"""
test_s2.py — Exhaustive verification of S2 policy on monotone traces.

S2 must:
- Decide all monotone traces.
- Be correct on them (matches Halts).
- Return UNKNOWN on at least one non-monotone trace (sanity).
"""

from proof_kernel import FiniteTrace, Halts, Monotone
from s2_policy import s2_decide, Verdict


def monotone_trace(bound: int, switchpoint: int) -> FiniteTrace:
    """
    bits = [0]*switchpoint + [1]*(bound-switchpoint)
    switchpoint in [0..bound], where switchpoint==bound => all zeros
    """
    bits = [False] * bound
    for i in range(switchpoint, bound):
        bits[i] = True
    bt = tuple(bits)
    return FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)


def test_s2_monotone_exhaustive(bound: int = 10):
    for sp in range(bound + 1):
        T = monotone_trace(bound, sp)
        assert Monotone(T)
        d = s2_decide(T)
        assert d.verdict in (Verdict.HALTS, Verdict.NOHALT)
        assert (d.verdict == Verdict.HALTS) == Halts(T)

    # sanity: ensure UNKNOWN on a non-monotone trace
    if bound >= 3:
        bits = [False] * bound
        bits[1] = True
        bt = tuple(bits)
        Tnm = FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)
        assert not Monotone(Tnm)
        dnm = s2_decide(Tnm)
        assert dnm.verdict == Verdict.UNKNOWN


if __name__ == "__main__":
    test_s2_monotone_exhaustive(10)
    print("PASS")
