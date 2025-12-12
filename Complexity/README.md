# Complexity: Time-Bounded Halting and P/NP

This folder extends the RevHalt framework with **time complexity**.

## Files

| File | Purpose |
|------|---------|
| `RevComplexity.lean` | Time-bounded halting, P and NP classes in RevHalt terms |

## Core Definitions

```lean
-- Time-bounded halting
def HaltsInTime (T : Trace) (t : ℕ) : Prop := ∃ n ≤ t, T n

-- Polynomial bound
def PolyBound (f : ℕ → ℕ) : Prop := ∃ k c, ∀ n, f n ≤ c * n^k + c

-- Class P
def inP (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ T f, PolyBound f ∧ DecidableInTime T L size f

-- Class NP  
def inNP (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ β R V g, PolyBound g ∧ ... ∧ (∀ x, L x ↔ ∃ y, R x y)
```

## Key Theorems

- `P_subset_NP` : P ⊆ NP
- `true_lang_in_P` : The always-true language is in P
- `false_lang_in_P` : The always-false language is in P

## Building

```bash
lake build Complexity
```
