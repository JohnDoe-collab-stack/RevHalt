"""
test_t3_corrected.py — Verification Suite for Corrected T3 Architecture
"""

from proof_kernel import FiniteTrace, Monotone, Halts
from s1_oracle import S1Oracle
from s2_extended import S2ExtendedProver
from t3_policy import T3Policy
from t3_types import Verdict

def mk_trace(bits):
    bt = tuple(bits)
    return FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), len(bt))

def test_s1_is_truth(bound=10):
    """S1 must match Halts exactly."""
    s1 = S1Oracle()
    # Test a few hand-picked traces
    # 1. Null trace (NOHALT)
    T0 = mk_trace([False]*bound)
    assert not Halts(T0)
    d0 = s1.decide(T0)
    assert d0.verdict == Verdict.NOHALT
    assert d0.source == "S1"
    
    # 2. Halting trace
    T1 = mk_trace([False, True] + [False]*(bound-2))
    assert Halts(T1)
    d1 = s1.decide(T1)
    assert d1.verdict == Verdict.HALTS
    
def test_s2_monotone_only(bound=10):
    """S2 must certify Monotone, and UNKNOWN otherwise."""
    s2 = S2ExtendedProver()
    
    # 1. Monotone
    Tm = mk_trace([False]*3 + [True]*(bound-3))
    assert Monotone(Tm)
    dm = s2.decide(Tm)
    assert dm.verdict == Verdict.HALTS
    assert dm.source == "S2"
    assert dm.cert["switchpoint"] == 3
    
    # 2. Non-Monotone
    Tnm = mk_trace([False, True, False] + [False]*(bound-3))
    assert not Monotone(Tnm)
    dnm = s2.decide(Tnm)
    assert dnm.verdict == Verdict.UNKNOWN
    
def test_s3_totality(bound=10):
    """S3 must be Total and Correct."""
    s3 = T3Policy()
    
    # Non-monotone trace -> Should route to S1 and return correct verdict
    Tnm = mk_trace([False, True, False] + [False]*(bound-3))
    assert Halts(Tnm)
    d = s3.decide(Tnm)
    assert d.verdict == Verdict.HALTS
    assert d.source == "S1" # correctly fell back to Oracle
    
    # Monotone trace -> Should route to S2
    Tm = mk_trace([False]*bound)
    d2 = s3.decide(Tm)
    assert d2.verdict == Verdict.NOHALT
    assert d2.source == "S2"

if __name__ == "__main__":
    test_s1_is_truth()
    test_s2_monotone_only()
    test_s3_totality()
    print("PASS: Corrected T3 Unit Tests")
