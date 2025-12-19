"""
s1_oracle.py — S1: The Oracle (Truth)

Wraps the Kernel's Rev0_K.
This IS the truth. It is not an ML approximation.
"""

from proof_kernel import FiniteTrace, Rev0_K, ExoticKit, Halts
from t3_types import Verdict, Decision

class S1Oracle:
    def __init__(self, kit=ExoticKit):
        self.kit = kit

    def decide(self, T: FiniteTrace) -> Decision:
        """
        Oracle always decides.
        T1 Guarantee: Rev0_K(K, T) <-> Halts(T) (on finite domain)
        """
        # In the finite domain, we can query the kit directly.
        # This is the "God View" or "Oracle Access".
        res = Rev0_K(self.kit, T)
        
        v = Verdict.HALTS if res else Verdict.NOHALT
        return Decision(
            verdict=v,
            source="S1",
            cert={"oracle_call": True, "kit": "ExoticKit"}
        )
