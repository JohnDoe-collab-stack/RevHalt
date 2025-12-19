"""
ML Policy Infrastructure

HaltingPolicy:
- Wraps a PyTorch(-like) model that maps bit-traces -> logit/prob.
- Provides selective decision with epsilon bands:
    p <= eps      -> NOHALT
    p >= 1-eps    -> HALTS
    else          -> ABSTAIN

compute_coverage_curve:
- Exhaustive evaluation over all 2^bound traces
- Produces exact coverage/accuracy metrics for eps in [0.00, 0.50]
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union

from proof_kernel import FiniteTrace, Halts

try:
    import torch
except Exception:
    torch = None


Decision = str  # "HALTS" | "NOHALT" | "ABSTAIN"


def _bits_from_trace(T: FiniteTrace) -> List[float]:
    return [1.0 if T.check(i) else 0.0 for i in range(T.bound)]


def _as_probability(output: Any) -> float:
    """
    Convert model output to probability in [0,1].
    Accepts:
      - float/int
      - torch tensor scalar
    If outside [0,1], treated as logit and passed through sigmoid.
    """
    if torch is None:
        raise RuntimeError("PyTorch not available; cannot interpret model outputs")

    if isinstance(output, (float, int)):
        p = float(output)
        if 0.0 <= p <= 1.0:
            return p
        return float(torch.sigmoid(torch.tensor(p)).item())

    # torch tensor
    t = output.reshape(-1)[0]
    p = float(t.item())
    if 0.0 <= p <= 1.0:
        return p
    return float(torch.sigmoid(t).item())


@dataclass
class HaltingPolicy:
    """
    Shippable policy wrapper for Bit-Trace mode.

    model(x) contract:
      - x is float tensor shape [1, bound]
      - output is probability in [0,1] OR a logit
    """
    model: Any
    bound: int
    eps: float = 0.10
    device: str = "cpu"

    def __post_init__(self) -> None:
        if not (0.0 <= self.eps <= 0.5):
            raise ValueError("eps must be in [0, 0.5]")
        if self.bound <= 0:
            raise ValueError("bound must be positive")
        if torch is None:
            raise RuntimeError("PyTorch not available; HaltingPolicy requires torch")

        # Put model in eval if available
        if hasattr(self.model, "eval"):
            self.model.eval()

    def prob(self, trace: Union[FiniteTrace, Sequence[bool]]) -> float:
        if isinstance(trace, FiniteTrace):
            bits = _bits_from_trace(trace)
            bound = trace.bound
        else:
            bits = [bool(b) for b in trace]
            bound = len(bits)

        if bound != self.bound:
            raise ValueError(f"trace bound mismatch: expected {self.bound}, got {bound}")

        x = torch.tensor([1.0 if b else 0.0 for b in bits], dtype=torch.float32).reshape(1, -1)
        x = x.to(torch.device(self.device))

        with torch.no_grad():
            out = self.model(x)

        return _as_probability(out)

    def decide(self, trace: Union[FiniteTrace, Sequence[bool]]) -> Tuple[Decision, float]:
        p = self.prob(trace)
        if p <= self.eps:
            return "NOHALT", p
        if p >= 1.0 - self.eps:
            return "HALTS", p
        return "ABSTAIN", p


def compute_coverage_curve(
    policy: HaltingPolicy,
    *,
    eps_grid: Optional[List[float]] = None,
) -> List[Dict[str, float]]:
    """
    Exhaustive curve over all 2^bound traces.
    Metrics are exact (no sampling).
    Returns list of dict rows, one per eps:
      eps, coverage, acc_on_covered, fp, fn
    """
    if eps_grid is None:
        eps_grid = [round(i / 100.0, 2) for i in range(0, 51)]  # 0.00 .. 0.50

    results: List[Dict[str, float]] = []
    bound = policy.bound

    # Pre-enumerate all traces once
    all_bits = list(product([False, True], repeat=bound))

    for eps in eps_grid:
        policy_eps = HaltingPolicy(policy.model, bound=bound, eps=float(eps), device=policy.device)

        covered = 0
        correct = 0
        fp = 0
        fn = 0

        for bits in all_bits:
            T = FiniteTrace(lambda n, bt=bits: bt[n], bound)
            truth = bool(Halts(T))
            decision, _p = policy_eps.decide(T)

            if decision == "ABSTAIN":
                continue

            covered += 1
            pred = (decision == "HALTS")
            if pred == truth:
                correct += 1
            else:
                if pred and (not truth):
                    fp += 1
                if (not pred) and truth:
                    fn += 1

        total = len(all_bits)
        coverage = covered / total if total else 0.0
        acc_cov = correct / covered if covered else 0.0

        results.append(
            {
                "eps": float(eps),
                "coverage": float(coverage),
                "acc_on_covered": float(acc_cov),
                "fp": float(fp),
                "fn": float(fn),
            }
        )

    return results
