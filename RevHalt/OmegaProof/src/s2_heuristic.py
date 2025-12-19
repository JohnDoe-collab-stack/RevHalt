"""
s2_heuristic.py — S2 with ML Guidance

Flow:
1. Try Monotone Logic (Standard S2).
2. If UNKNOWN: Ask ML WitnessModel for Top-K candidates.
3. Verify candidates using S2.certify_witness().
4. If valid witness found -> Return S2 Decision.
5. Else -> Return UNKNOWN.
"""

from typing import List
import torch
from proof_kernel import FiniteTrace
from t3_types import Decision, Verdict
from s2_extended import S2ExtendedProver
from ml_witness import WitnessModel

class S2Heuristic:
    def __init__(self, prover: S2ExtendedProver, model: WitnessModel, device="cpu", k=3):
        self.prover = prover
        self.model = model
        self.device = device
        self.k = k
        self.model.to(device)
        self.model.eval()

    def _tensorize(self, T: FiniteTrace):
        bits = [1.0 if T.check(i) else 0.0 for i in range(T.bound)]
        return torch.tensor([bits], dtype=torch.float32, device=self.device)

    def decide(self, T: FiniteTrace) -> Decision:
        # 1. Base S2 (Monotone)
        d_base = self.prover.decide(T)
        if d_base.verdict != Verdict.UNKNOWN:
            return d_base

        # 2. ML Guidance
        x = self._tensorize(T)
        with torch.no_grad():
            candidates = self.model.predict_topk(x, k=self.k) # Shape [1, k]
            candidates = candidates[0].tolist()
        
        # 3. Verify Candidates
        for idx in candidates:
            # If model predicts NULL (idx == bound), skip (cannot certify NOHALT via witness)
            if idx == T.bound:
                continue
                
            res = self.prover.certify_witness(T, idx)
            if res:
                # Upgrading source info to indicate ML assistance
                return Decision(
                    verdict=res.verdict, 
                    source="S2+ML", 
                    cert={**res.cert, "proposed_by_ml": True}
                )

        # 4. Failed to find witness
        return Decision(
            verdict=Verdict.UNKNOWN,
            source="S2",
            cert={"reason": "ML failed to find witness"}
        )
