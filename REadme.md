Voici une version légèrement resserrée et corrigée, sans changer le contenu mathématique ni le ton général.

````markdown
# RevHalt: Formal Verification of Reverse-Halting Theory

A Lean 4 formalization of the **Reverse-Halting (Rev)** framework, establishing canonicity, impossibility, and complementarity theorems for search-theoretic verification.

## Overview

This project formalizes three core theorems about the Rev predicate — a cumulative, observable counterpart to the classical Halting predicate:

| Theorem | Statement                        | Status   |
|---------|----------------------------------|----------|
| **T1**  | Canonicity of Rev                | ✅ Proven |
| **T2**  | Impossibility of Internalization | ✅ Proven |
| **T3**  | Complementarity (Weak + Strong)  | ✅ Proven |

All proofs are verified by the Lean 4 kernel with **no `sorry`** statements.

---

## Mathematical Background

### The Rev Predicate

A **trace** is a temporal evolution of a property:

```text
Trace    := ℕ → Prop
Halts(T) := ∃ n, T(n)
up(T)(n) := ∃ k ≤ n, T(k)       -- cumulative (monotone) projection
Rev_K(T) := K.Proj(up(T))      -- observable via kit K
````

**Key insight**: When `K` detects monotone processes, `Rev_K` is extensionally equal to `Halts` on all traces.

### Observation Kits

An `RHKit` is an abstract observation interface:

```lean
structure RHKit where
  Proj : (ℕ → Prop) → Prop
```

Monotone detection is captured by:

```lean
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : ℕ → Prop, Monotone X → (K.Proj X ↔ ∃ n, X n)
```

So `K` is free to behave arbitrarily on non-monotone families, but must coincide with plain existence on monotone ones.

---

## Theorems

### T1: Canonicity

**Trace level.** For any kit `K` satisfying `DetectsMonotone`, Rev exactly captures Halts:

```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T
```

Thus all such kits define the **same** halting predicate on traces: they belong to a single “universality class” for halting.

**Semantic level.** Under a dynamic bridge from semantics to traces, semantic consequence coincides with the Rev-based verdict:

```lean
theorem T1_semantics (K : RHKit) (hK : DetectsMonotone K) 
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ
```

Here:

* `SemConsequences Sat Γ φ` means “`φ` is in the semantic closure `CloE(Sat, Γ)`”,
* `verdict_K LR Γ φ` is the stabilized Rev-verdict on the trace `LR Γ φ`.

So in each admissible reference frame `(Sat, LR)`, semantic consequence is realized as a **robust dynamic halt**.

---

### T2: Impossibility of Internalization

**Statement.** In any Turing–Gödel context `ctx`, there is no internal halting predicate that is simultaneously total, correct, and complete for the *real* halting predicate `ctx.RealHalts`:

```lean
theorem T2_impossibility (ctx : TuringGodelContext' Code PropT) :
    ¬ ∃ _ : InternalHaltingPredicate ctx, True
```

An `InternalHaltingPredicate` is a predicate `H : Code → PropT` satisfying:

* **totality**    : `∀ e, Provable(H e) ∨ Provable(Not (H e))`
* **correctness**: `RealHalts e → Provable(H e)`
* **completeness**: `¬ RealHalts e → Provable(Not (H e))`

The proof uses a diagonal program provided by:

```lean
ctx.diagonal_program :
  ∀ H : Code → PropT, ∃ e, RealHalts e ↔ Provable (Not (H e))
```

This is an abstract, but fully formal, Gödel–Turing style obstruction: no consistent recursive theory can internalize the canonical halting predicate `RealHalts` as a perfect decision predicate.

---

### T3: Complementarity

T3 describes how sound theories relate to an external notion of truth (e.g. the canonical halting predicate) as **partial but extendable views**.

#### T3-Weak (Extension by Truth)

Any sound partial theory can be strictly extended by adding a true statement it does not yet prove, while preserving soundness:

```lean
theorem T3_weak_extension {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop)        -- meta-level truth predicate
    (_ : ∀ p, ctx.Provable p → Truth p) -- soundness of the base system
    (T0 : Set PropT)              -- initial theory
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (p_undef : PropT)
    (h_p_true : Truth p_undef)    -- p is true
    (_ : ¬ ctx.Provable p_undef)  -- p not (yet) provable
    : ∃ T1 : Set PropT, T0 ⊆ T1 ∧ (∀ p ∈ T1, Truth p) ∧ p_undef ∈ T1
```

This is the basic complementarity pattern: any sound incomplete theory can be strictly extended by adding an external truth.

#### T3-Strong (Disjoint Families)

**Conditional theorem.** Assume an infinite family of independent halting instances (abstracted as `InfiniteIndependentHalting`) and a partition of their index set. Then we can build a family of sound theories whose “newly decided” instances are pairwise disjoint:

```lean
theorem T3_strong {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop)
    (encode_halt : Code → PropT)
    (encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT)
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (indep : InfiniteIndependentHalting Code PropT ctx)
    (partition : Partition indep.Index) :
    ∃ (TheoryFamily : ℕ → Set PropT),
        (∀ n, T0 ⊆ TheoryFamily n) ∧
        (∀ n, ∀ p ∈ TheoryFamily n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j)
```

Here, disjointness is expressed at the level of the partitioned index set: each `TheoryFamily n` decides a different “slice” of the independent halting instances.

> **Important:** T3-Strong is *parametric* in `InfiniteIndependentHalting`: it is a structural/combinatorial theorem. The existence of such a family in concrete theories (PA, ZF, etc.) is a separate, classical question in recursion theory / arithmetic.

---

## Epistemological Significance

T2 and T3 together clarify the position of Rev (and its associated canonical halting predicate) with respect to ZFC-strength systems:

* **T2 (Impossibility):**
  No consistent recursively axiomatized theory of strength comparable to ZFC can internalize the canonical halting predicate `RealHalts` (instantiated as `Rev` on traces) as a total, correct, and complete predicate.

* **T3 (Complementarity):**
  Any such sound theory is a **partial view** of the external halting truth:
  it can always be strictly extended by adding further true halting facts, and (under suitable independence hypotheses) these extensions can be organized into complementary families.

In this sense:

* formal systems like ZFC approximate the external Rev-based halting truth but never fully capture it;
* Rev (via its canonical halting predicate) acts not as a competitor to ZFC, but as an **epistemic complement** and reference frame: a meta-level notion of truth relative to which internal theories can be compared, extended, and combined.

---

## Concrete Instances (`RevHaltInstances.lean`)

### RecursiveKit

The canonical instantiation of `RHKit`:

```lean
def RecursiveKit : RHKit where
  Proj := fun X => ∃ n, X n

theorem RecursiveKit_DetectsMonotone : DetectsMonotone RecursiveKit := by
  intro X _hMono
  rfl

theorem Rev_RecursiveKit_eq_Halts : ∀ T, Rev0_K RecursiveKit T ↔ Halts T :=
  T1_traces RecursiveKit RecursiveKit_DetectsMonotone
```

Here `RecursiveKit` simply interprets `Proj` as bare existence. T1 then shows that `Rev0_K` is exactly `Halts` for all traces.

### DynamicBridge for Propositional Logic

For a finite set of atoms, we define a propositional calculus and a tautology checker. The corresponding trace is:

```lean
def TautologySearchTrace (Atom : Type) [DecidableEq Atom] [Fintype Atom]
    (φ : PropFormula Atom) : Trace :=
  fun _ => IsTautology Atom φ
```

Then:

```lean
theorem PropLogic_DynamicBridge (Atom : Type) [DecidableEq Atom] [Fintype Atom] :
    ∀ φ : PropFormula Atom, IsTautology Atom φ ↔ Halts (TautologySearchTrace Atom φ)
```

This is a simple but concrete instance of `DynamicBridge`: semantic tautology ↔ halting of a trace.

### TuringGodelFromModel

We derive a `TuringGodelContext'` from an abstract computability model:

```lean
structure ComputabilityModel where
  Code : Type
  Program : Code → (ℕ → Option ℕ)
  recursion_theorem : ∀ f : Code → Code, ∃ e, Program e = Program (f e)
  diagonal_halting : ∀ P : Code → Prop, ∃ e, (Program e 0).isSome ↔ ¬ P e
  nonHaltingCode : Code
  nonHalting : ¬ (Program nonHaltingCode 0).isSome
```

Internal propositions are halting statements:

```lean
inductive HaltProp (M : ComputabilityModel) where
  | halts : M.Code → HaltProp M
  | notHalts : M.Code → HaltProp M
```

We then construct:

```lean
def TuringGodelFromModel (M : ComputabilityModel) :
    TuringGodelContext' M.Code (HaltProp M)
```

Design choices:

* `HaltProp` has only `halts` / `notHalts` constructors (no ad hoc `.false` case).
* `FalseT` is defined as “`nonHaltingCode` halts”, which is never provable by construction.
* All axioms of `TuringGodelContext'` (`consistent`, `absurd`, `diagonal_program`) are **fully derived** from the model.

This shows that the abstract Turing–Gödel context used in T2 is realizable from a standard computability schema.

---

## Project Structure

```text
RevHalt/
├── RevHalt.lean          # Core definitions and theorems (T1, T2, T3)
├── RevHaltInstances.lean # Concrete instantiations
├── lakefile.lean         # Build configuration
├── lean-toolchain        # Lean version
└── README.md             # This file
```

---

## Building

```bash
# Clone the repository
git clone <repo-url>
cd RevHalt

# Build the project
lake build
```

**Requirements**: Lean 4 with Mathlib (configured via `lakefile.lean`).

## Verification

```bash
lake build RevHalt RevHaltInstances
# Build completed successfully.
# Exit code: 0
```

No warnings, no errors, no `sorry`.

---

## Design Philosophy

1. **Explicit Hypotheses**
   All assumptions (monotonicity, bridges, independence, etc.) are explicit parameters, not hidden axioms.

2. **Clean Abstractions**
   Core interfaces (`RHKit`, `DynamicBridge`, `TuringGodelContext'`) are modular and reusable.

3. **Concrete Grounding**
   `RevHaltInstances.lean` demonstrates that the abstract framework is actually realizable (recursive kit, logical bridge, computability model).

4. **No Hacks**
   The `HaltProp` design removes edge cases; all properties are proved without ad hoc constructions.

---

## Citation

If you use this work, please cite:

```text
RevHalt: A Lean 4 Formalization of Reverse-Halting Theory
```

John Doe, December 12 2025

---

## License

MIT License

```
```
