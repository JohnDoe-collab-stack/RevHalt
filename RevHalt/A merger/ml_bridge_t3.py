"""
ml_bridge_t3.py — Additive T3 extensions over ml_bridge.py (no kernel changes)

This module keeps the existing ml_bridge.py intact, and adds the dataset generator
needed for T3-style training (with monotone/non-monotone tags).

If you want, you can later *merge* this into ml_bridge.py; but keeping it separate
makes the "kernel freeze" constraint obvious.
"""

from __future__ import annotations

from typing import Tuple

from proof_kernel import FiniteTrace, Halts, Monotone

try:
    import torch
except Exception:  # pragma: no cover
    torch = None


def generate_halting_dataset(
    bound: int,
    n_samples: int,
    p_monotone: float = 0.0,
    seed: int | None = None,
) -> Tuple["torch.Tensor", "torch.Tensor", "torch.Tensor"]:
    """
    Returns (X, y, is_monotone).

    X: FloatTensor [n_samples, bound] with {0,1}.
    y: FloatTensor [n_samples, 1] with {0,1} = Halts.
    is_monotone: BoolTensor [n_samples].

    Sampling:
    - With probability p_monotone, sample a monotone trace (switchpoint form).
    - Otherwise sample uniform random bit-trace.
    """
    if torch is None:
        raise RuntimeError("PyTorch is required for dataset generation (ml_bridge_t3).")
    if seed is not None:
        torch.manual_seed(seed)

    if p_monotone <= 0.0:
        is_m = torch.zeros(n_samples, dtype=torch.bool)
    elif p_monotone >= 1.0:
        is_m = torch.ones(n_samples, dtype=torch.bool)
    else:
        is_m = (torch.rand(n_samples) < p_monotone)

    X = torch.zeros((n_samples, bound), dtype=torch.float32)

    # monotone via switchpoint
    if is_m.any():
        idx = torch.nonzero(is_m).view(-1)
        sps = torch.randint(0, bound + 1, (idx.numel(),), dtype=torch.int64)
        for row, sp in zip(idx.tolist(), sps.tolist()):
            if sp < bound:
                X[row, sp:] = 1.0

    # non-monotone uniform
    if (~is_m).any():
        idx = torch.nonzero(~is_m).view(-1)
        X[idx] = torch.randint(0, 2, (idx.numel(), bound), dtype=torch.int64).float()

    y = (X.sum(dim=1, keepdim=True) > 0.0).float()
    return X, y, is_m
