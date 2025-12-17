import RevHalt.Dynamics.Instances.CollatzTrace
import RevHalt.Theory.Complementarity
import RevHalt.Kinetic.MasterClosure
import RevHalt.Kinetic.System
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Lattice

namespace RevHalt

open Set
open RevHalt.Dynamics.Instances.CollatzTrace

/-!
# RevHalt.Dynamics.Instances.CollatzIndependence

**Proper (non-degenerate) connection of Collatz to InfiniteIndependentHalting.**

## Key Insight

To connect Collatz to T3-strong without cheating on `Provable`:
- Don't define `Provable := False` (that's degenerate)
- Don't use bounded `CollatzBounded n n` (that's not Collatz)
- Instead, require an **encoding** `ℕ → Code` with `RealHalts(code n) ↔ CollatzHolds' n`

## Main Definitions

- `CollatzEmbedding ctx`: An encoding of Collatz into the ambient Code type
- `CollatzIndependent ctx E`: The resulting InfiniteIndependentHalting family

## Usage

Given a `ctx : TuringGodelContext' Code PropT` and an `E : CollatzEmbedding ctx`,
you can build `CollatzIndependent ctx E` and use it with `T3_strong`, `PartFresh`, etc.
-/

/--
**CollatzEmbedding**: A correct encoding of the Collatz problem into a TuringGodelContext'.

This is the bridge between:
- The abstract `CollatzHolds' n` (defined via `collatzTrace'`)
- The ambient `RealHalts` predicate of the context

To construct this, you need to:
1. Define `code : ℕ → Code` (compile Collatz(n) into a code)
2. Prove `inj` (codes are distinct)
3. Prove `agree` (RealHalts matches CollatzHolds')
-/
structure CollatzEmbedding {Code PropT : Type} (ctx : TuringGodelContext' Code PropT) where
  code  : ℕ → Code
  inj   : Function.Injective code
  agree : ∀ n : ℕ, ctx.RealHalts (code n) ↔ CollatzHolds' n

/--
**CollatzIndependent**: From a correct encoding, Collatz provides an infinite family.

This is the proper way to instantiate `InfiniteIndependentHalting` for Collatz:
- Index = ℕ
- family = E.code
- haltsTruth = CollatzHolds'
- halts_agree = E.agree
-/
def CollatzIndependent {Code PropT : Type}
    (ctx : TuringGodelContext' Code PropT) (E : CollatzEmbedding ctx) :
    InfiniteIndependentHalting Code PropT ctx where
  Index := ℕ
  InfiniteIndex := inferInstance
  family := E.code
  distinct := E.inj
  haltsTruth := CollatzHolds'
  halts_agree := E.agree

/-!
## Connection to Kinetic Layer (VerifiableContext)

If you have a `VerifiableContext` with propositions `C : ℕ → PropT` such that
`LR ∅ (C n) = collatzTrace' n`, then you can connect Truth to CollatzHolds'.
-/

/--
If `LR ∅ (C n)` is definitionally the Collatz trace, then
`Truth(C n) ↔ CollatzHolds' n`.
-/
theorem truth_collatz_iff
    {Code PropT : Type} (V : VerifiableContext Code PropT)
    (C : ℕ → PropT)
    (hLR : ∀ n : ℕ, V.LR ∅ (C n) = collatzTrace' n) :
    ∀ n : ℕ, V.Truth (C n) ↔ CollatzHolds' n := by
  intro n
  have hb := V.h_bridge (C n)
  simpa [hLR n, CollatzHolds'_iff_halts] using hb

/--
If `Truth(C n)` holds but `C n` is not provable, then `C n ∈ Gap V`.

This is the Gödelian content: true but unprovable Collatz instances are in the Gap.
-/
theorem gap_of_collatz_true_not_provable
    {Code PropT : Type} (V : VerifiableContext Code PropT)
    (C : ℕ → PropT)
    (n : ℕ)
    (hTrue : V.Truth (C n))
    (hNP : ¬ V.Provable (C n)) :
    C n ∈ Gap V := by
  have : C n ∈ GapTruth V := ⟨hTrue, hNP⟩
  simpa [Gap_eq_GapTruth] using this

/-!
## Partition for T3-Strong

A simple singleton partition for use with the machinery.
-/

/-- Singleton partition: Part m = {m}. -/
def CollatzSingletonPartition : Partition ℕ where
  Parts := fun m => {m}
  disjoint := by
    intro n m hnm
    rw [disjoint_iff]
    ext x
    constructor
    · intro ⟨hn, hm⟩
      exact hnm (hn.symm.trans hm)
    · intro h
      exact h.elim

/-- Each part is nonempty. -/
theorem collatzSingletonPartition_nonempty :
    ∀ m : ℕ, ∃ i : ℕ, i ∈ CollatzSingletonPartition.Parts m :=
  fun m => ⟨m, rfl⟩

/-!
## Summary

This file provides the **correct** (non-degenerate) interface:

1. `CollatzEmbedding ctx`: The hard part - encoding Collatz into Code
2. `CollatzIndependent ctx E`: The InfiniteIndependentHalting family
3. `truth_collatz_iff`: Connection to VerifiableContext
4. `gap_of_collatz_true_not_provable`: Collatz in Gap if true but unprovable

**What this does NOT do**:
- Prove Collatz
- Construct `CollatzEmbedding` (that requires formalizing Collatz as a Partrec code)
- Prove freshness (that requires showing Collatz is not provable in T0)

**What this enables**:
- If you provide `E : CollatzEmbedding ctx`, you get access to the full T3-strong machinery
- The connection is semantically correct (uses real CollatzHolds', not bounded approximation)
-/

end RevHalt
