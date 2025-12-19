# eval_ml.py
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Optional, Tuple, Any, List
from itertools import product

from proof_kernel import FiniteTrace, Halts, Monotone, up
from ml_bridge import kit_from_model

try:
    import torch
except Exception:
    torch = None


def _trace_from_bits(bits: List[bool]) -> FiniteTrace:
    bt = tuple(bits)
    bound = len(bt)
    return FiniteTrace(lambda n, bt=bt: bt[n], bound)


def verify_determinism(K, T: FiniteTrace, n_runs: int = 10) -> None:
    """Ensures K.Proj(T) is stable across repeated calls."""
    first = K.Proj(T)
    for _ in range(n_runs - 1):
        if K.Proj(T) != first:
            raise RuntimeError("Non-deterministic Kit.Proj detected")


def accuracy(K, bound: int, n_samples: int, *, seed: Optional[int] = None) -> float:
    """Monte Carlo accuracy of K.Proj on random traces."""
    if torch is None:
        raise RuntimeError("PyTorch not available")

    gen = torch.Generator()
    if seed is not None:
        gen.manual_seed(int(seed))

    # sample random traces
    X = torch.randint(0, 2, (n_samples, bound), generator=gen, dtype=torch.int64)
    correct = 0
    for i in range(n_samples):
        bits = [bool(int(v)) for v in X[i].tolist()]
        T = _trace_from_bits(bits)
        y = Halts(T)
        pred = K.Proj(T)
        if bool(pred) == bool(y):
            correct += 1
    return correct / n_samples


def abstention_rate(K, bound: int, n_samples: int, epsilon: float, *, seed: Optional[int] = None) -> Tuple[float, float]:
    """
    Decision coverage/abstention using model probability p:
      - decide if p <= epsilon or p >= 1-epsilon
      - abstain otherwise

    Returns: (coverage, accuracy_on_covered)
    """
    if torch is None:
        raise RuntimeError("PyTorch not available")
    if not (0.0 <= epsilon <= 0.5):
        raise ValueError("epsilon must be in [0, 0.5]")

    gen = torch.Generator()
    if seed is not None:
        gen.manual_seed(int(seed))

    X = torch.randint(0, 2, (n_samples, bound), generator=gen, dtype=torch.int64).float()
    covered = 0
    covered_correct = 0

    # require underlying model to exist: K is RHKit built by kit_from_model(model)
    # so K.Proj computes thresholded decision only; here we need probabilities.
    # therefore pass in model directly, or wrap an object exposing model.
    model = getattr(K, "_model", None)
    if model is None:
        raise ValueError("abstention_rate requires a Kit with attribute _model (see build_kit_with_model)")

    with torch.no_grad():
        logits_or_probs = model(X)
        p = logits_or_probs.reshape(-1, 1)
        # if outside [0,1], treat as logits
        if (p.min().item() < 0.0) or (p.max().item() > 1.0):
            p = torch.sigmoid(p)

    for i in range(n_samples):
        bits = [bool(int(v)) for v in X[i].tolist()]
        T = _trace_from_bits(bits)
        y = bool(Halts(T))
        pi = float(p[i].item())

        if pi <= epsilon:
            covered += 1
            covered_correct += (y is False)
        elif pi >= 1.0 - epsilon:
            covered += 1
            covered_correct += (y is True)
        else:
            pass  # abstain

    coverage = covered / n_samples
    acc_cov = (covered_correct / covered) if covered > 0 else 0.0
    return coverage, acc_cov


def monotone_mismatch_rate(K, bound: int, n_samples: int, *, seed: Optional[int] = None) -> float:
    """
    Monte Carlo mismatch rate restricted to monotone traces.
    For each sampled monotone trace X: mismatch if K.Proj(X) != Halts(X).
    """
    if torch is None:
        raise RuntimeError("PyTorch not available")

    gen = torch.Generator()
    if seed is not None:
        gen.manual_seed(int(seed))

    mismatches = 0
    seen = 0

    # sample monotone traces by choosing a switch-point s in [0..bound]
    # bits = 0..0 then 1..1
    s = torch.randint(0, bound + 1, (n_samples,), generator=gen, dtype=torch.int64)
    for i in range(n_samples):
        sp = int(s[i].item())
        bits = [False] * sp + [True] * (bound - sp)
        T = _trace_from_bits(bits)
        assert Monotone(T)
        seen += 1
        if bool(K.Proj(T)) != bool(Halts(T)):
            mismatches += 1

    return mismatches / seen if seen > 0 else 0.0


def balanced_accuracy(K, bound: int, n_samples: int, *, seed: Optional[int] = None) -> float:
    """Balanced accuracy over random traces: 0.5*(TPR+TNR)."""
    if torch is None:
        raise RuntimeError("PyTorch not available")

    gen = torch.Generator()
    if seed is not None:
        gen.manual_seed(int(seed))

    X = torch.randint(0, 2, (n_samples, bound), generator=gen, dtype=torch.int64)

    tp = tn = fp = fn = 0
    for i in range(n_samples):
        bits = [bool(int(v)) for v in X[i].tolist()]
        T = _trace_from_bits(bits)
        y = bool(Halts(T))
        p = bool(K.Proj(T))
        if y and p:
            tp += 1
        elif (not y) and (not p):
            tn += 1
        elif (not y) and p:
            fp += 1
        else:
            fn += 1

    tpr = tp / (tp + fn) if (tp + fn) else 0.0
    tnr = tn / (tn + fp) if (tn + fp) else 0.0
    return 0.5 * (tpr + tnr)


def monotone_detects_monotone_failure_rate(K, bound: int) -> float:
    """
    Exact failure rate on the entire monotone family (there are bound+1 traces):
    bits = 0..0 then 1..1 with switchpoint sp in [0..bound].
    """
    failures = 0
    total = 0
    for sp in range(bound + 1):
        bits = [False] * sp + [True] * (bound - sp)
        T = _trace_from_bits(bits)
        total += 1
        if bool(K.Proj(T)) != bool(Halts(T)):
            failures += 1
    return failures / total if total else 0.0


    return failures / total if total else 0.0


def exact_metrics(K, bound: int):
    """
    Exact metrics over all 2^bound traces (feasible for bound<=12).
    Returns: (acc, bacc, tpr, tnr)
    """
    tp = tn = fp = fn = 0

    for bits in product([False, True], repeat=bound):
        T = _trace_from_bits(list(bits))
        y = bool(Halts(T))
        p = bool(K.Proj(T))

        if y and p:
            tp += 1
        elif (not y) and (not p):
            tn += 1
        elif (not y) and p:
            fp += 1
        else:
            fn += 1

    acc = (tp + tn) / (tp + tn + fp + fn)
    tpr = tp / (tp + fn) if (tp + fn) else 0.0
    tnr = tn / (tn + fp) if (tn + fp) else 0.0
    bacc = 0.5 * (tpr + tnr)

    return acc, bacc, tpr, tnr


def monotone_failure_cases(K, bound: int):
    """
    Exact list of monotone traces (switchpoint family) where K.Proj != Halts.
    Returns list of dicts with: sp, bits, truth, pred.
    """
    failures = []
    for sp in range(bound + 1):
        bits = [False] * sp + [True] * (bound - sp)
        T = _trace_from_bits(bits)
        truth = bool(Halts(T))
        pred = bool(K.Proj(T))
        if pred != truth:
            failures.append(
                {"sp": sp, "bits": bits, "truth": truth, "pred": pred}
            )
    return failures


def build_kit_with_model(model: Any, threshold: float = 0.5):
    """
    Returns an RHKit from model and attaches _model for abstention metrics.
    """
    K = kit_from_model(model, threshold=threshold)
    # attach for eval routines
    setattr(K, "_model", model)
    return K
