"""
s2_extended.py — S2 Prover with Witness Checking

Capabilities:
1. Monotone Logic (Switchpoint)
2. Witness Check (Index Verification)
"""

from typing import Optional, Any, Dict
from proof_kernel import FiniteTrace, Monotone
from t3_types import Verdict, Decision

def _monotone_switchpoint(T: FiniteTrace) -> int:
    for i in range(T.bound):
        if T.check(i):
            return i
    return T.bound

class S2ExtendedProver:
    def decide(self, T: FiniteTrace) -> Decision:
        """
        Base capability: Only Monotone logic.
        """
        if Monotone(T):
            sp = _monotone_switchpoint(T)
            halts = (sp < T.bound)
            return Decision(
                verdict=Verdict.HALTS if halts else Verdict.NOHALT,
                source="S2",
                cert={"logic": "Monotone", "switchpoint": sp}
            )
        return Decision(
            verdict=Verdict.UNKNOWN,
            source="S2",
            cert={"reason": "Non-Monotone"}
        )

    def certify_witness(self, T: FiniteTrace, index: int) -> Optional[Decision]:
        """
        Try to certify HALTS using a specific witness index.
        This is an O(1) check if index is provided.
        """
        # strict bounds check
        if index < 0 or index >= T.bound:
            return None # Invalid index
            
        if T.check(index):
            # Found a True bit at 'index'. This proves Halting.
            return Decision(
                verdict=Verdict.HALTS,
                source="S2", # Internal S2 decision
                cert={"logic": "Witness", "index": index, "assisted_by": "ML"}
            )
            
        return None # Verification failed (False at index)
        return None # Verification failed (False at index)

def verify_cert(T: FiniteTrace, d: Decision) -> bool:
    """
    Universal Certificate Verifier (Anti-Cheat Rule B).
    
    Ensures that any S2 decision is locally verifiable without an Oracle.
    
    Rules:
    1. If source is S2/S2+ML, cert must be valid locally.
    2. Rule A: If logic="Witness", verdict must be HALTS.
    3. Rule B: Check must match trace data.
    """
    if d.source not in ("S2", "S2+ML"):
        return True # External/Oracle decisions are trusted by definition (T3)
        
    logic = d.cert.get("logic")
    
    if logic == "Monotone":
        # Monotone logic check
        if not Monotone(T): return False
        sp = d.cert["switchpoint"]
        # Check consistency
        if d.verdict == Verdict.HALTS:
            return sp < T.bound and T.check(sp)
        else:
            return sp == T.bound
            
    elif logic == "Witness":
        # Anti-Cheat Rule A
        if d.verdict != Verdict.HALTS:
            return False # Witness can only prove Halting
            
        # Anti-Cheat Rule B (Local Check)
        idx = d.cert["index"]
        if idx < 0 or idx >= T.bound: return False
        return T.check(idx)
        
    return False # Unknown logic type
