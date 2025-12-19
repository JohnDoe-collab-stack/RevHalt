"""
s1_kit.py — T3 Architecture Component S1 (External Evaluator / ML Kit)

S1 is *not* assumed internalisable. It provides an external evaluation signal
(score/logit/confidence) and an epsilon-based selective decision rule.

Important: S1 is NEVER used to decide monotone traces in the T3 policy;
monotone traces are routed to S2 (proof-like layer).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional

from proof_kernel import FiniteTrace

try:
    import torch
    import torch.nn as nn
except Exception:  # pragma: no cover
    torch = None
    nn = None


class Verdict(str, Enum):
    HALTS = "HALTS"
    NOHALT = "NOHALT"
    ABSTAIN = "ABSTAIN"


@dataclass(frozen=True)
class S1Eval:
    prob: float        # sigmoid(logit)
    logit: float
    confidence: float  # in [0,1], higher => more confident
    bound: int


def _sigmoid(x: float) -> float:
    # local sigmoid to keep deterministic even if torch is absent
    import math
    return 1.0 / (1.0 + math.exp(-x))


class S1Kit:
    """
    Wraps a (PyTorch) model that maps bit-trace vectors -> logit.
    """

    def __init__(self, model, bound: int, device: str = "cpu"):
        self.model = model
        self.bound = bound
        self.device = device

        if torch is not None and hasattr(model, "to"):
            self.model.to(device)
        if torch is not None and hasattr(model, "eval"):
            self.model.eval()

    def _tensorize(self, T: FiniteTrace):
        if torch is None:
            raise RuntimeError("PyTorch is required for S1Kit.evaluate but is not available.")
        if T.bound != self.bound:
            raise ValueError(f"Trace bound {T.bound} != S1 bound {self.bound}")
        x = torch.tensor([1.0 if T.check(i) else 0.0 for i in range(self.bound)], dtype=torch.float32)
        return x.to(self.device)

    @torch.no_grad() if torch is not None else (lambda f: f)
    def evaluate(self, T: FiniteTrace) -> S1Eval:
        """
        Returns raw evaluation information (no decision).
        """
        if torch is None:
            raise RuntimeError("PyTorch is required for S1Kit.evaluate but is not available.")

        x = self._tensorize(T).unsqueeze(0)  # [1, bound]
        out = self.model(x)
        # allow shape [1] or [1,1]
        logit = float(out.view(-1)[0].item())
        prob = _sigmoid(logit)
        confidence = abs(prob - 0.5) * 2.0
        return S1Eval(prob=prob, logit=logit, confidence=confidence, bound=T.bound)

    @staticmethod
    def decide(ev: S1Eval, eps: float = 0.10, threshold: float = 0.5) -> Verdict:
        """
        Selective decision:
        - If confidence < eps => ABSTAIN.
        - Else => HALTS if prob >= threshold else NOHALT.
        """
        if ev.confidence < eps:
            return Verdict.ABSTAIN
        return Verdict.HALTS if ev.prob >= threshold else Verdict.NOHALT
