# RevHalt: Formal Verification of Reverse-Halting Theory

A Lean 4 formalization of the **Reverse-Halting (Rev)** framework, establishing canonicity, impossibility, and complementarity theorems for search-theoretic verification.

## Overview

This project formalizes three core theorems about the Rev predicate — a cumulative, observable counterpart to the classical Halting predicate:

| Theorem | Statement | Status |
|---------|-----------|--------|
| **T1** | Canonicity of Rev | ✅ Proven |
| **T2** | Impossibility of Internalization | ✅ Proven |
| **T3** | Complementarity (Weak + Strong) | ✅ Proven |

All proofs are verified by the Lean 4 kernel with **no `sorry`** statements.

---

## Mathematical Background

### The Rev Predicate

Given a trace `T : ℕ → Prop` representing the evolution of a computation:

```
Halts(T) := ∃ n, T(n)
up(T)(n) := ∃ k ≤ n, T(k)     -- cumulative projection
Rev_K(T) := K.Proj(up(T))     -- observable via kit K
```

**Key insight**: When `K` detects monotone properties, `Rev_K` exactly captures `Halts`.

### Observation Kits

An `RHKit` is an abstract observation interface:

```lean
structure RHKit where
  Proj : (ℕ → Prop) → Prop

def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : ℕ → Prop, Monotone X → (K.Proj X ↔ ∃ n, X n)
```

---

## Theorems

### T1: Canonicity

**Statement**: For any kit `K` satisfying `DetectsMonotone`, Rev exactly captures Halts.

```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T
```

**Semantic Bridge**: Under the `DynamicBridge` hypothesis, semantic consequence coincides with Rev-based verification:

```lean
theorem T1_semantics (K : RHKit) (hK : DetectsMonotone K) 
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ
```

### T2: Impossibility of Internalization

**Statement**: No internal predicate can be simultaneously Total, Correct, and Complete for the real halting predicate.

```lean
theorem T2_impossibility (ctx : TuringGodelContext' Code PropT) :
    ¬ ∃ _ : InternalHaltingPredicate ctx, True
```

**Mechanism**: Uses the diagonal argument via `ctx.diagonal_program`.

### T3: Complementarity

#### T3-Weak (Extension by Truth)

Any sound partial theory can be extended by adding a true undecidable statement:

```lean
theorem T3_weak_extension ... :
    ∃ T1 : Set PropT, T0 ⊆ T1 ∧ (∀ p ∈ T1, Truth p) ∧ p_undef ∈ T1
```

#### T3-Strong (Disjoint Families)

**Conditional theorem**: Given an infinite family of independent halting instances and a partition, we can construct disjoint sound theories:

```lean
theorem T3_strong ... (indep : InfiniteIndependentHalting Code PropT ctx)
    (partition : Partition indep.Index) :
    ∃ (TheoryFamily : ℕ → Set PropT),
        (∀ n, T0 ⊆ TheoryFamily n) ∧
        (∀ n, ∀ p ∈ TheoryFamily n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j)
```

> **Note**: T3-Strong is parameterized by `InfiniteIndependentHalting`, an explicit structural hypothesis. The existence of such a family in specific systems (PA, ZF) is a separate result from recursion theory.

---

## Concrete Instances (`RevHaltInstances.lean`)

### RecursiveKit

The canonical instantiation of `RHKit`:

```lean
def RecursiveKit : RHKit where
  Proj := fun X => ∃ n, X n

theorem RecursiveKit_DetectsMonotone : DetectsMonotone RecursiveKit := rfl

theorem Rev_RecursiveKit_eq_Halts : ∀ T, Rev0_K RecursiveKit T ↔ Halts T
```

### DynamicBridge for Propositional Logic

For finite propositional logic with tautology checking:

```lean
theorem PropLogic_DynamicBridge (Atom : Type) [DecidableEq Atom] [Fintype Atom] :
    ∀ φ : PropFormula Atom, IsTautology Atom φ ↔ Halts (TautologySearchTrace Atom φ)
```

### TuringGodelFromModel

A clean derivation of `TuringGodelContext'` from an abstract computability model:

```lean
structure ComputabilityModel where
  Code : Type
  Program : Code → (ℕ → Option ℕ)
  recursion_theorem : ∀ f : Code → Code, ∃ e, Program e = Program (f e)
  diagonal_halting : ∀ P : Code → Prop, ∃ e, (Program e 0).isSome ↔ ¬ P e
  nonHaltingCode : Code
  nonHalting : ¬ (Program nonHaltingCode 0).isSome

def TuringGodelFromModel (M : ComputabilityModel) : 
    TuringGodelContext' M.Code (HaltProp M)
```

**Key design**: 
- `HaltProp` has only `halts`/`notHalts` constructors (no `.false` hack)
- `FalseT` is defined as `halts nonHaltingCode`
- All axioms (`consistent`, `absurd`, `diagonal_program`) are **fully derived**

---

## Project Structure

```
RevHalt/
├── RevHalt.lean          # Core definitions and theorems (T1, T2, T3)
├── RevHaltInstances.lean # Concrete instantiations
├── lakefile.lean         # Build configuration
├── lean-toolchain        # Lean version
└── README.md             # This file
```

## Building

```bash
# Clone the repository
git clone <repo-url>
cd RevHalt

# Build the project
lake build
```

**Requirements**: Lean 4 with Mathlib dependency.

## Verification

```bash
lake build RevHalt RevHaltInstances
# Build completed successfully.
# Exit code: 0
```

No warnings, no errors, no `sorry`.

---

## Design Philosophy

1. **Explicit Hypotheses**: All assumptions are parameters, not hidden axioms.
2. **Clean Abstractions**: `RHKit`, `TuringGodelContext'`, `DynamicBridge` are modular.
3. **Concrete Grounding**: `RevHaltInstances.lean` shows the abstract framework is realizable.
4. **No Hacks**: The `HaltProp` approach eliminates edge cases without compromising generality.

---

## Citation

If you use this work, please cite:

```
RevHalt: A Lean 4 Formalization of Reverse-Halting Theory
```

---

## License

MIT License
