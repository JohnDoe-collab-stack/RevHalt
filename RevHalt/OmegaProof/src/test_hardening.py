"""
test_hardening.py — Final Lockdown Suite for T3 Integrity

Checks:
1. Strict Witness Bounds (Negative, Out of Bound indices rejected by S2).
2. Provenance Semantics ("S2" source for ML-assisted certs).
3. Oracle Agreement (S1 Oracle matches Halts(T) universally).
"""

from proof_kernel import FiniteTrace, Halts
from s2_extended import S2ExtendedProver
from s1_oracle import S1Oracle
from t3_types import Verdict, Decision

def mk_trace(bits):
    bt = tuple(bits)
    return FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), len(bt))

def test_strict_witness_bounds(bound=6):
    """S2 must reject invalid indices even if T.check() is permissive."""
    prover = S2ExtendedProver()
    # Trace with a 1 at index 2
    T = mk_trace([False, False, True, False, False, False]) 
    
    # 1. Valid Witness
    d = prover.certify_witness(T, 2)
    assert d is not None
    assert d.verdict == Verdict.HALTS
    
    # 2. Invalid Index (Negative)
    d_neg = prover.certify_witness(T, -1)
    assert d_neg is None
    
    # 3. Invalid Index (Out of Bound)
    d_oob = prover.certify_witness(T, bound)
    assert d_oob is None
    
    d_oob2 = prover.certify_witness(T, bound + 100)
    assert d_oob2 is None

def test_provenance_semantics(bound=6):
    """Decisions made via witness check must be sourced S2."""
    prover = S2ExtendedProver()
    T = mk_trace([False, True] + [False]*(bound-2))
    
    d = prover.certify_witness(T, 1)
    assert d.source == "S2"
    assert d.cert["logic"] == "Witness"
    assert d.cert["assisted_by"] == "ML"

def test_oracle_universal_agreement(bound=8):
    """S1 Oracle must match Halts(T) exactly on entire domain."""
    from itertools import product
    oracle = S1Oracle()
    
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        T = FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), len(bt))
        truth = Halts(T)
        d = oracle.decide(T)
        
        expected = Verdict.HALTS if truth else Verdict.NOHALT
        assert d.verdict == expected, f"Oracle disagreed with Truth on {T}"

def test_verify_cert_rules(bound=6):
    """Enforce Rule A and Rule B via verify_cert."""
    from s2_extended import verify_cert
    
    prover = S2ExtendedProver()
    # Trace: 0 0 1 0...
    T = mk_trace([False, False, True, False, False, False])
    
    # 1. Valid Witness
    d_valid = prover.certify_witness(T, 2)
    assert verify_cert(T, d_valid) is True
    
    # 2. Forge a Fake Cert (Rule B violation)
    # Claim index 0 is witness (it is False)
    d_fake = Decision(Verdict.HALTS, "S2", {"logic": "Witness", "index": 0})
    assert verify_cert(T, d_fake) is False
    
    # 3. Forge a NOHALT Witness (Rule A violation)
    d_bad_logic = Decision(Verdict.NOHALT, "S2", {"logic": "Witness", "index": 2})
    assert verify_cert(T, d_bad_logic) is False

if __name__ == "__main__":
    test_strict_witness_bounds()
    test_provenance_semantics()
    test_oracle_universal_agreement()
    test_verify_cert_rules()
    print("PASS: Hardening Suite Verified.")
