"""
t3_policy.py — S3: The Total System (S2 ∪ S1)

Routing:
S2 (Prover) -> If Decided, Return.
S1 (Oracle) -> Fallback (Always Decides).

Provenance is preserved.
"""

from proof_kernel import FiniteTrace
from t3_types import Decision, Verdict
from s1_oracle import S1Oracle
from s1_oracle import S1Oracle
from s2_extended import S2ExtendedProver

class T3Policy:
    def __init__(self):
        self.s1 = S1Oracle()
        self.s2 = S2ExtendedProver()

    def decide(self, T: FiniteTrace) -> Decision:
        # 1. Ask Internal S2
        d2 = self.s2.decide(T)
        if d2.verdict != Verdict.UNKNOWN:
            return d2
        
        # 2. Fallback to External S1 (Oracle)
        d1 = self.s1.decide(T)
        return d1
