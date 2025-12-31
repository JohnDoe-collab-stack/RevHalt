# The Machine-Verified Ordinal Boundary

## The Main Theorem

```lean
-- OrdinalMechanical.lean
theorem dichotomy_all_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬ P)
```

The total dichotomy for traces is **exactly equivalent to Excluded Middle (EM)**.

Verified with **zero axioms** (`#print axioms dichotomy_all_iff_em`).

---

## The Double Gap Analysis

The boundary is not a simple ordinal jump. It involves **TWO** simultaneous jumps:

| Dimension | Finite Stage ($n$) | Limit Stage ($\omega$) |
|-----------|--------------------|------------------------|
| **Ordinal** | Finite | Infinite (accumulation) |
| **Class** | Decidable Traces | Arbitrary Traces |

### 1. The Ordinal Jump ($n \to \omega$)
- Finite stages (for decidable traces) are constructive.
- The limit implies quantification over all finite stages.

### 2. The Class Jump (Decidable $\to$ Prop)
- **Decidable Traces** (`ℕ → Bool`): The limit yields LPO-like principles (weaker than EM).
- **Arbitrary Traces** (`ℕ → Prop`): The limit yields full EM.

### Why Arbitrary Traces?
The equivalence `Dichotomy ↔ EM` relies on the ability to encode **any proposition** into a trace:
```lean
def constTrace (P : Prop) : Trace := fun _ => P
```
Without this encoding (i.e., if we restricted to decidable traces), we could not derive EM.

---

## Machine Verification Summary

| Theorem | Trace Class | Ordinal | Result | Axioms |
|---------|-------------|---------|--------|--------|
| `dichotomy_up_to` | Decidable | Finite ($n$) | Constructive | 0 |
| `limit_stage_is_em` | **Arbitrary** | Limit ($\omega$) | **= EM** | 0 |

The formalization (`OrdinalMechanical.lean`) proves that the gap between "Constructive finite checks" and "Classical limit dichotomy" is exactly the content of Excluded Middle.

---

## Files
- `RevHalt/Theory/OrdinalMechanical.lean` — The rigorous proof with Double Gap
- `RevHalt/Theory/OrdinalBoundary.lean` — (Deprecated) Initial exploration
