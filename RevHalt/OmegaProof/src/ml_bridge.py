# ml_bridge.py
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional, Any, Dict

from proof_kernel import FiniteTrace, RHKit, Formula, QuestionType, formula_to_trace, Halts

try:
    import torch
    from torch import Tensor
except Exception:  # allow running without torch installed
    torch = None
    Tensor = Any  # type: ignore


def trace_from_model(
    model: Any,
    formula: Formula,
    q_type: QuestionType,
    *,
    bound: Optional[int] = None,
    threshold: float = 0.5,
) -> FiniteTrace:
    """
    Build a FiniteTrace from a PyTorch-like model that scores each valuation index n.

    Contract for model:
      - callable(model_input) -> scalar in [0,1] or logits
      - We call model on integer indices 0..bound-1, as a tensor of shape [1]
      - Output interpreted as probability via sigmoid if not already in [0,1]

    Semantics:
      - SAT: trace(n)=True if model believes valuation n satisfies formula (>= threshold)
      - TAUT: trace(n)=True if model believes valuation n is a counterexample (>= threshold)
    """
    if torch is None:
        raise RuntimeError("PyTorch not available; install torch to use trace_from_model")

    # Use kernel’s canonical bound for the formula unless overridden
    base_T = formula_to_trace(formula, q_type)
    eff_bound = base_T.bound if bound is None else int(bound)
    if eff_bound <= 0:
        raise ValueError("bound must be positive")

    # We do NOT call Halts here; we only build a trace.
    def check(n: int) -> bool:
        if n < 0 or n >= eff_bound:
            return False
        x = torch.tensor([n], dtype=torch.long)
        y = model(x)

        # normalize output to a float probability
        if isinstance(y, (float, int)):
            p = float(y)
        else:
            y_t = y.reshape(-1)[0]
            p = float(y_t.item())

        # if p is outside [0,1], treat as logits
        if p < 0.0 or p > 1.0:
            p = float(torch.sigmoid(torch.tensor(p)).item())

        return p >= threshold

    return FiniteTrace(check, eff_bound)


def kit_from_model(
    model: Any,
    *,
    threshold: float = 0.5,
) -> RHKit:
    """
    Wrap a model into a Kit. This Kit is NON-CANONICAL by default.

    Contract for model:
      - model(bits_tensor) -> scalar probability/logit for "Halts"
      - bits_tensor is float tensor shape [bound] or [1, bound]

    Proj(T):
      - builds bit-vector [T(0),...,T(bound-1)] and feeds it to the model
      - returns model_pred >= threshold
    """
    if torch is None:
        raise RuntimeError("PyTorch not available; install torch to use kit_from_model")

    def proj(T: FiniteTrace) -> bool:
        bits = [1.0 if T.check(i) else 0.0 for i in range(T.bound)]
        x = torch.tensor(bits, dtype=torch.float32).reshape(1, -1)
        y = model(x)

        if isinstance(y, (float, int)):
            p = float(y)
        else:
            y_t = y.reshape(-1)[0]
            p = float(y_t.item())

        if p < 0.0 or p > 1.0:
            p = float(torch.sigmoid(torch.tensor(p)).item())

        return p >= threshold

    return RHKit(Proj=proj)


from typing import Tuple, Optional

def generate_halting_dataset(
    bound: int,
    n_samples: int,
    *,
    seed: Optional[int] = None,
    device: Optional[str] = None,
    p_monotone: float = 0.5,
) -> "Tuple[Tensor, Tensor]":
    """
    Mixed sampling:
      - with prob p_monotone: monotone trace via switchpoint
      - else: uniform random trace
    Labels: y = OR(bits)
    """
    if torch is None:
        raise RuntimeError("PyTorch not available; install torch to use generate_halting_dataset")
    if bound <= 0:
        raise ValueError("bound must be positive")
    if n_samples <= 0:
        raise ValueError("n_samples must be positive")
    if not (0.0 <= p_monotone <= 1.0):
        raise ValueError("p_monotone must be in [0,1]")

    gen = torch.Generator()
    if seed is not None:
        gen.manual_seed(int(seed))

    dev = torch.device(device) if device is not None else torch.device("cpu")

    X = torch.empty((n_samples, bound), device=dev, dtype=torch.float32)

    u = torch.rand((n_samples,), generator=gen, device=dev)
    mono_mask = u < float(p_monotone)

    # monotone: choose switchpoint sp in [0..bound]
    if bool(mono_mask.any().item()):
        idx = mono_mask.nonzero(as_tuple=False).reshape(-1)
        s = torch.randint(0, bound + 1, (idx.numel(),), generator=gen, device=dev, dtype=torch.int64)
        for j in range(idx.numel()):
            sp = int(s[j].item())
            row = int(idx[j].item())
            if sp > 0:
                X[row, :sp] = 0.0
            if sp < bound:
                X[row, sp:] = 1.0

    # random
    if bool((~mono_mask).any().item()):
        idx = (~mono_mask).nonzero(as_tuple=False).reshape(-1)
        X[idx] = torch.randint(0, 2, (idx.numel(), bound), generator=gen, device=dev, dtype=torch.int64).float()

    y = (X.sum(dim=1, keepdim=True) > 0.0).float()
    return X, y
