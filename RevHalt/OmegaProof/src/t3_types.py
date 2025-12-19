"""
t3_types.py — Type Definitions for Corrected T3 Architecture

S1 = Oracle (Truth)
S2 = Prover (Internal)
S3 = Total (S2 ∪ S1)
"""

from enum import Enum
from dataclasses import dataclass
from typing import Any, Dict, Optional

class Verdict(str, Enum):
    HALTS = "HALTS"
    NOHALT = "NOHALT"
    UNKNOWN = "UNKNOWN"
    # No ABSTAIN in S3 (Total)

@dataclass(frozen=True)
class Decision:
    verdict: Verdict
    source: str          # "S1" (Oracle) | "S2" (Prover)
    cert: Dict[str, Any] # Proof certificate or Oracle signature
