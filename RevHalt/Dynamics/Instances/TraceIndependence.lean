import RevHalt.Base.Trace
import RevHalt.Theory.Complementarity
import RevHalt.Theory.ComplementarityMeasure
import RevHalt.Theory.ComplementarityMeasureBridge

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt.Dynamics.Instances.TraceIndependence

Generic "n kept all along" independence pattern.

- Index = parameter (kept on both sides)
- code = compiler(Index)
- truth/halts side = Halts (trace Index)
- no fuel-freezing (time stays inside `Halts` as ∃ t)
-/

namespace RevHalt.Dynamics.Instances.TraceIndependence

open Set
open RevHalt

section

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)

/-- Compilation package: `i ↦ code i` whose real-halting matches `Halts (trace i)`. -/
structure TraceCompiler where
  Index : Type
  InfiniteIndex : Infinite Index
  trace : Index → Trace
  code : Index → Code
  code_inj : Function.Injective code
  halts_agree : ∀ i, ctx.RealHalts (code i) ↔ Halts (trace i)

namespace TraceCompiler

/-- Induced `InfiniteIndependentHalting` family from a compiler. -/
def indep (comp : TraceCompiler (ctx := ctx)) :
    InfiniteIndependentHalting Code PropT ctx where
  Index := comp.Index
  InfiniteIndex := comp.InfiniteIndex
  family := comp.code
  distinct := comp.code_inj
  haltsTruth := fun i => Halts (comp.trace i)
  halts_agree := comp.halts_agree

end TraceCompiler

/-- Convenience: Singleton partition for `Index = ℕ` (identity injection). -/
def singletonPartitionNat : Partition ℕ :=
  RevHalt.partitionOfNatInjection id Function.injective_id

/-- Main gate (generic): compiler + fresh parts ⇒ unbounded proposition-level width. -/
theorem gate_unbounded_width
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT)
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (comp : TraceCompiler (ctx := ctx))
    (f : ℕ → comp.Index) (hf : Function.Injective f)
    [DecidablePred (comp.indep (ctx := ctx)).haltsTruth]
    (hFreshAll : ∀ m : ℕ,
      PartFresh (ctx := ctx)
        (indep := comp.indep (ctx := ctx))
        (partition := RevHalt.partitionOfNatInjection f hf)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
        T0 m) :
    ∀ k : ℕ, Width Truth T0 k := by
  exact strong_fresh_implies_unbounded_width
    (ctx := ctx)
    (indep := comp.indep (ctx := ctx))
    (partition := RevHalt.partitionOfNatInjection f hf)
    Truth encode_halt encode_not_halt
    h_encode_correct h_encode_correct_neg
    T0 h_T0_sound
    hFreshAll

end

end RevHalt.Dynamics.Instances.TraceIndependence
