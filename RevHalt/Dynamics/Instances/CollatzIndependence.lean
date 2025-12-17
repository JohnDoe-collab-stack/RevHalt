import RevHalt.Dynamics.Instances.CollatzTrace
import RevHalt.Theory.Complementarity
import RevHalt.Theory.ComplementarityMeasure
import RevHalt.Theory.ComplementarityMeasureBridge

import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint
import Mathlib.Data.Nat.Lattice

/-!
# RevHalt.Dynamics.Instances.CollatzIndependence

Collatz "n kept all along":

- index = n : ℕ
- code = collatzCode n : Code
- truth/halts side = Halts (collatzTrace' n) = CollatzHolds' n
- no (n,n) fuel-freezing; the fuel is the existential time inside `Halts`.
-/

namespace RevHalt.Dynamics.Instances.CollatzIndependence

open Set
open RevHalt
open RevHalt.Dynamics.Instances.CollatzTrace

section

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)

/-- Compilation package: "Collatz(n)" ↦ a code whose real-halting matches the Collatz trace. -/
structure CollatzCompiler where
  collatzCode : ℕ → Code
  inj : Function.Injective collatzCode
  halts_agree : ∀ n, ctx.RealHalts (collatzCode n) ↔ Halts (collatzTrace' n)

namespace CollatzCompiler

/-- The induced InfiniteIndependentHalting family (index = ℕ, family = collatzCode). -/
def indep (comp : CollatzCompiler (ctx := ctx)) :
    InfiniteIndependentHalting Code PropT ctx where
  Index := ℕ
  InfiniteIndex := inferInstance
  family := comp.collatzCode
  distinct := comp.inj
  haltsTruth := fun n => Halts (collatzTrace' n)
  halts_agree := comp.halts_agree

end CollatzCompiler

/-- Singleton partition on ℕ: Parts m = {m}. -/
def singletonPartition : Partition ℕ where
  Parts := fun m => {m}
  disjoint := by
    intro n m hnm
    simpa [Set.disjoint_singleton] using hnm

/--
Main "gate" (n kept all along):

If every part contributes a *fresh* decided Collatz proposition (via strongEncode),
then unbounded proposition-level width follows.
-/
theorem collatz_gate_unbounded_width
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT)
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (comp : CollatzCompiler (ctx := ctx))
    [DecidablePred (comp.indep (ctx := ctx)).haltsTruth]
    (hFreshAll : ∀ m : ℕ,
      PartFresh (ctx := ctx)
        (indep := comp.indep (ctx := ctx))
        (partition := singletonPartition)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
        T0 m) :
    ∀ k : ℕ, Width Truth T0 k := by
  -- just instantiate the generic bridge theorem
  exact strong_fresh_implies_unbounded_width
    (ctx := ctx)
    (indep := comp.indep (ctx := ctx))
    (partition := singletonPartition)
    Truth encode_halt encode_not_halt
    h_encode_correct h_encode_correct_neg
    T0 h_T0_sound
    hFreshAll

/--
Convenient simplification (singleton partition):

Freshness at part m reduces to:
`strongEncode ... m ∉ T0` (because Parts m = {m}).
-/
theorem partFresh_singleton_iff
    (_ : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (T0 : Set PropT)
    (comp : CollatzCompiler (ctx := ctx))
    [DecidablePred (comp.indep (ctx := ctx)).haltsTruth] :
    (∀ m : ℕ,
        PartFresh (ctx := ctx)
          (indep := comp.indep (ctx := ctx))
          (partition := singletonPartition)
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
          T0 m)
    ↔
    (∀ m : ℕ,
        strongEncode (ctx := ctx) (indep := comp.indep (ctx := ctx))
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) m ∉ T0) := by
  constructor
  · intro h m
    rcases h m with ⟨i, hi, hfresh⟩
    -- hi : i ∈ {m} ⇒ i = m
    have : i = m := by simpa [singletonPartition, Set.mem_singleton_iff] using hi
    simpa [this] using hfresh
  · intro h m
    refine ⟨m, rfl, h m⟩

end

end RevHalt.Dynamics.Instances.CollatzIndependence
