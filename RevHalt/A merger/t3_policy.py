"""
t3_policy.py — T3-aligned Halting Policy (S2 ⊔ S1)

Routing:
- First query S2 (internalisable). If it decides, return that with source="S2".
- Otherwise query S1 (external evaluator) and apply selective decision rule.
- Output includes provenance and (optionally) evaluation confidence.

This is the operational counterpart of the T3 decomposition:
S3 = S2 ∪ S1 (with provenance).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional

from proof_kernel import FiniteTrace

from s2_policy import s2_decide, Decision as S2Decision, Verdict as S2Verdict
from s1_kit import S1Kit, S1Eval, Verdict as S1Verdict


@dataclass(frozen=True)
class Decision:
    verdict: str                 # "HALTS" | "NOHALT" | "ABSTAIN" | "UNKNOWN"
    source: str                  # "S2" | "S1"
    cert: Dict[str, Any]         # certificates / metadata
    confidence: Optional[float]  # only for S1 decisions


class T3HaltingPolicy:
    def __init__(self, s1: S1Kit, eps: float = 0.10):
        self.s1 = s1
        self.eps = eps

    def evaluate(self, T: FiniteTrace) -> S1Eval:
        """
        Pure evaluation path (S1 only). No decision, no routing.
        """
        return self.s1.evaluate(T)

    def decide(self, T: FiniteTrace) -> Decision:
        """
        Full T3 decision with routing and provenance.
        """
        d2: S2Decision = s2_decide(T)
        if d2.verdict != S2Verdict.UNKNOWN:
            return Decision(
                verdict=d2.verdict.value,
                source="S2",
                cert=d2.cert,
                confidence=None,
            )

        # frontier: ask S1
        ev = self.s1.evaluate(T)
        v1 = self.s1.decide(ev, eps=self.eps)
        return Decision(
            verdict=v1.value,
            source="S1",
            cert={"prob": ev.prob, "logit": ev.logit, "eps": self.eps},
            confidence=ev.confidence,
        )
