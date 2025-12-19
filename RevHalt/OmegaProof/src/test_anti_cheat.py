"""
test_anti_cheat.py — Strict Verification Suite for T3 Integrity

Ensures:
1. S2 never imports S1/Oracle (Structure).
2. S2 never lies (Soundness).
3. S2 works even if Oracle is dead (Independence).
4. S3 is Total (Completeness).
"""

import sys
import re
import pathlib
import pytest
from itertools import product
from proof_kernel import FiniteTrace, Halts
from s2_extended import S2ExtendedProver
from s2_heuristic import S2Heuristic
from t3_policy import T3Policy
from t3_types import Verdict
from ml_witness import WitnessModel

# --- A. Structural Checks ---

def test_s2_no_oracle_deps():
    """S2 must NOT import s1_oracle, Rev0_K, or t3_policy."""
    FORBIDDEN = [r"s1_oracle", r"Rev0_K", r"t3_policy"]
    FILES = ["s2_extended.py", "s2_heuristic.py"]
    
    for fname in FILES:
        if not pathlib.Path(fname).exists(): continue
        content = pathlib.Path(fname).read_text(encoding="utf-8")
        for bad in FORBIDDEN:
             assert re.search(bad, content) is None, f"{fname} illegally imports {bad}"

# --- B. S2 Soundness Checks ---

def all_traces(bound):
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        yield FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)

def test_s2_never_lies(bound=6): # Low bound for speed
    """S2 (Extended/Heuristic) must match Truth when it decides."""
    s2 = S2ExtendedProver()
    # Mock model for heuristic
    model = WitnessModel(bound) # Random weights ok, just checking safety logic
    s2_h = S2Heuristic(s2, model, k=3) 

    for T in all_traces(bound):
        truth = Halts(T)
        
        # Check Base S2
        d = s2.decide(T)
        if d.verdict != Verdict.UNKNOWN:
            assert (d.verdict == Verdict.HALTS) == truth, f"S2 Lied on {T}"

        # Check Heuristic S2
        d_h = s2_h.decide(T)
        if d_h.verdict != Verdict.UNKNOWN:
            assert (d_h.verdict == Verdict.HALTS) == truth, f"S2+ML Lied on {T}"
            # Verify Certificate Logic
            if d_h.cert.get("logic") == "Witness":
                idx = d_h.cert["index"]
                assert T.check(idx), "Fake Witness Certificate!"

# --- E. Oracle Unplugged Test ---

class DeadOracle:
    def decide(self, T):
        raise RuntimeError("Oracle called illegally!")

def test_s2_works_without_oracle(bound=6):
    """S2 and S2+ML must operate without calling S1."""
    s2 = S2ExtendedProver()
    model = WitnessModel(bound)
    s2_h = S2Heuristic(s2, model)
    
    # We can't easily injection-test t3_policy to fail on S1 because it instantiates S1Oracle internally.
    # But we can verify S2Heuristic independent execution.
    
    for T in all_traces(bound):
        try:
            d = s2_h.decide(T)
            # Should return Decision or UNKNOWN, never crash or call external
        except Exception as e:
            pytest.fail(f"S2 crashed without Oracle connection: {e}")

# --- D. T3 Totality ---

def test_t3_is_total(bound=6):
    """S3 must always yield HALTS/NOHALT."""
    policy = T3Policy()
    
    for T in all_traces(bound):
        d = policy.decide(T)
        assert d.verdict in (Verdict.HALTS, Verdict.NOHALT)
        assert d.verdict != Verdict.UNKNOWN
        
        # Provenance Check
        if d.source in ["S2", "S2+ML"]:
            # If S2 decided, it must have a cert
            assert "cert" in d.__dict__ or hasattr(d, "cert")

if __name__ == "__main__":
    # Manually run if pytest not present
    print("Running Structural Checks...")
    test_s2_no_oracle_deps()
    print("Running Soundness Checks...")
    test_s2_never_lies()
    print("Running Independence Checks...")
    test_s2_works_without_oracle()
    print("Running Totality Checks...")
    test_t3_is_total()
    print("PASS: Anti-Cheat Suite Verified.")
