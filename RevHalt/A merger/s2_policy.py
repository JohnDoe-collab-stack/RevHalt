"""
s2_policy.py — T3 Architecture Component S2 (Internalisable / Proof-like)

S2 is the *internalisable* layer: it only decides what the base system can decide
with a transparent certificate. In our finite trace setting, we take "internalisable"
to mean:

- If the trace is Monotone (in the finite-window sense used by proof_kernel.Monotone),
  then HALTS/NOHALT is decidable with a simple structural certificate.
- Otherwise, S2 returns UNKNOWN (it does not guess).

This matches the T3 intent: S2 is the sound base corpus; S1 will extend it on the frontier.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict

from proof_kernel import FiniteTrace, Monotone, Halts


class Verdict(str, Enum):
    HALTS = "HALTS"
    NOHALT = "NOHALT"
    UNKNOWN = "UNKNOWN"
    ABSTAIN = "ABSTAIN"  # included for uniformity (policy can map UNKNOWN->ABSTAIN)


@dataclass(frozen=True)
class Decision:
    verdict: Verdict
    source: str  # "S2" / "S1" / "S3"
    cert: Dict[str, Any]


def _monotone_switchpoint(T: FiniteTrace) -> int:
    """
    For a monotone trace, return the smallest index sp such that T(sp)=True,
    or sp == bound if T is all-false.

    This is a *certificate witness* (explanatory), not required for correctness.
    """
    for i in range(T.bound):
        if T.check(i):
            return i
    return T.bound


def s2_decide(T: FiniteTrace) -> Decision:
    """
    Internalisable decision procedure.

    - If not Monotone(T): UNKNOWN.
    - If Monotone(T): decide exactly Halts(T), with a switchpoint certificate.
    """
    if not Monotone(T):
        return Decision(
            verdict=Verdict.UNKNOWN,
            source="S2",
            cert={"reason": "non-monotone", "bound": T.bound},
        )

    sp = _monotone_switchpoint(T)
    halts = (sp < T.bound)  # equivalent to Halts(T) for monotone traces
    # We still compute Halts(T) for defensive consistency checks:
    halts_check = Halts(T)
    if halts != halts_check:
        # Should never happen; if it does, we include evidence.
        return Decision(
            verdict=Verdict.UNKNOWN,
            source="S2",
            cert={
                "reason": "internal inconsistency",
                "sp": sp,
                "halts_by_sp": halts,
                "halts_by_scan": halts_check,
            },
        )

    return Decision(
        verdict=Verdict.HALTS if halts else Verdict.NOHALT,
        source="S2",
        cert={"monotone": True, "switchpoint": sp, "bound": T.bound},
    )
