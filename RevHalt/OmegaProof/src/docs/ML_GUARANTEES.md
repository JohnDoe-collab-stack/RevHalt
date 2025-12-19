# ML Guarantees

This project implements a strictly verified finite-domain RevHalt kernel and an ML extension layer.
The kernel remains unchanged (frozen) and is exhaustively verified on the finite trace domain.

## 1. Kernel Guarantees (proof_kernel.py)

### Domain
- Traces are finite: `T : {0..bound-1} -> Bool`.
- `FiniteTrace.check(n)` is total and returns `False` for `n<0` or `n>=bound`.

### Definitions (finite analogs of Lean)
- `Halts(T)` := `∃ n < bound, T(n)`.
- `up(T)(n)` := `∃ k ≤ n, T(k)` (within the finite domain).
- `Monotone(T)` := `∀ n,m < bound, n ≤ m → (T(n) → T(m))`.
- `RHKit` with `Proj : Trace -> Bool`.
- `Rev0_K(K,T)` := `K.Proj(up(T))`.

### Exhaustive Verification
For a fixed `bound`, the strict test suite verifies universally:
- Bridge: `Halts(up(T)) ↔ Halts(T)`.
- DetectsMonotone condition on monotone traces: `Monotone(X) → (K.Proj(X) == Halts(X))`.
- T1 (finite): `Rev0_K(K,T) ↔ Halts(T)` for all traces `T` in the finite domain.
- Exoticity witness exists: a non-monotone `T` where `K.Proj(T) != Halts(T)`.

These guarantees are exact and exhaustive on the finite domain tested (e.g., `bound=10` gives 1024 traces).

## 2. ML Kit Guarantees (Bit-Trace Mode)

### What the ML Kit is
- The ML model is trained to approximate `Halts(T)` from raw bit traces `T`.
- `kit_from_model(model)` yields an `RHKit` whose `Proj(T)` is a thresholded model prediction.

### Status
- The ML Kit is **not assumed canonical by construction**.
- Canonical behavior is enforced empirically/training-wise (e.g., monotone regularization, null-trace margin).
- Exact finite-domain evaluation is used to detect:
  - confusion matrix (TP/TN/FP/FN),
  - monotone switchpoint failures,
  - error localization by Hamming weight.

## 3. Selective Decision Guarantees (Policy Layer)

### Policy Object
`HaltingPolicy` wraps a model and exposes:
- `decide(trace) -> HALTS | NOHALT | ABSTAIN`
using a confidence band parameter `eps`:

- if `p <= eps` then `NOHALT`
- if `p >= 1-eps` then `HALTS`
- otherwise `ABSTAIN`

where `p` is the model probability (sigmoid(logit) if necessary).

### Exact Coverage Curve
`compute_coverage_curve(policy, bound)` enumerates all `2^bound` traces and returns exact:
- coverage = fraction of traces not abstained upon,
- accuracy on covered decisions,
- FP/FN on covered decisions.

This turns the ML component into a controllable extension:
- the kernel remains the ground-truth reference for definitions,
- the ML layer provides probabilistic guidance,
- the policy makes explicit when it refuses to decide.

## 4. Practical Interpretation

- Kernel: fully verified decision mechanics in the finite domain.
- ML Kit: a heuristic approximation of `Halts(T)` (may be conservative).
- Policy: explicit non-black-box behavior: it can abstain near the boundary where the ML model is uncertain.
