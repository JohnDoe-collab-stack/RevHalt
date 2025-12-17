import RevHalt.Theory.Complementarity
import RevHalt.Theory.ComplementarityMeasure
import RevHalt.Theory.ComplementarityMeasureBridge

/-!
# RevHalt.Theory.CollatzComplementarity

Application of the weak+strong+bridge framework to Collatz-type problems.

## Main Results

- `CollatzPartFresh`: Freshness condition specialized to Collatz instances
- `collatz_unbounded_width`: If all parts are Collatz-fresh, we get unbounded width
- `CollatzHasUnboundedWidth`: The complete "Collatz gate" predicate encapsulating
  the full existential package (reservoir + partition + freshness + width)
- `collatzHasUnboundedWidth_of_freshness`: Constructor for the gate

## Key Insight

"Complementarity" means using **both** weak and strong:
- **Strong** provides the structural grid (infinite independent family + partition)
- **Weak** provides strictness (each part contributes genuine new information)
- **Bridge** converts PartFresh → Width

The operational question for Collatz becomes:
> Does there exist a strong reservoir `indep` and a partition of `indep.Index`
> such that, relative to T₀, each part contains an index whose encoding
> coincides with a Collatz instance C(n) and is fresh (C(n) ∉ T₀)?
-/

namespace RevHalt

open Set

section CollatzComplementarity

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)
variable (indep : InfiniteIndependentHalting Code PropT ctx)
variable (partition : Partition indep.Index)
variable [DecidablePred indep.haltsTruth]

variable (Truth : PropT → Prop)
variable (T0 : Set PropT)
variable (h_T0_sound : ∀ p ∈ T0, Truth p)

-- The Collatz family of propositions
variable (C : ℕ → PropT)

-- Encodings for halts / not halts
variable (encode_halt encode_not_halt : Code → PropT)
variable (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
variable (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))

/-!
## Collatz-specific freshness

The junction point where weak and strong meet for Collatz:
in each part m, there exists an index i from the strong reservoir
such that `strongEncode i` equals some Collatz instance `C n`
and this instance is fresh (not in T₀).
-/

/-- Freshness condition specialized to Collatz: part m contains a fresh Collatz instance. -/
def CollatzPartFresh (m : ℕ) : Prop :=
  ∃ (i : indep.Index) (n : ℕ),
    i ∈ partition.Parts m ∧
    strongEncode (ctx := ctx) (indep := indep)
      (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) i = C n ∧
    C n ∉ T0

/--
If every part is Collatz-fresh, we obtain proposition-level `Width k` for all k.

This is exactly the measured "weak→strong distance" instantiated to Collatz:
weak typically provides "at least 1 strict extension",
while strong+fresh provides "for all k, k strict extensions".
-/
theorem collatz_unbounded_width
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (hFreshAll : ∀ m : ℕ, CollatzPartFresh ctx indep partition T0 C
        encode_halt encode_not_halt m) :
    ∀ k : ℕ, Width Truth T0 k := by
  intro k
  -- Reduce to PartFresh from the Bridge via the equality to C n
  have hPF : ∀ m : ℕ,
      PartFresh (ctx := ctx) (indep := indep) (partition := partition)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) T0 m := by
    intro m
    rcases hFreshAll m with ⟨i, n, him, hEq, hNot⟩
    refine ⟨i, him, ?_⟩
    -- strongEncode i ∉ T0 because it equals C n and C n ∉ T0
    simpa [hEq] using hNot
  -- Now the bridge gives ∀ k, Width ... k
  exact strong_fresh_implies_unbounded_width
    (ctx := ctx) (indep := indep) (partition := partition)
    Truth encode_halt encode_not_halt
    h_encode_correct h_encode_correct_neg T0 h_T0_sound hPF k

end CollatzComplementarity

/-!
## The Collatz Gate: Complete Existential Package

This definition encapsulates the full quantifier package as a single `Prop`
that can be targeted as the "Collatz gate" in the framework.

Structure:
1. ∃ indep (the strong reservoir)
2. ∃ partition (over indep.Index)
3. ∃ Decidable instance
4. ∧ Freshness (∀ m, CollatzPartFresh m)
5. ∧ Width (∀ k, Width Truth T0 k)
-/

/-- Collatz has unbounded width relative to T0 via some strong reservoir + partition + freshness. -/
def CollatzHasUnboundedWidth
    {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop) (T0 : Set PropT) (C : ℕ → PropT)
    (encode_halt encode_not_halt : Code → PropT) : Prop :=
  ∃ (indep : InfiniteIndependentHalting Code PropT ctx),
  ∃ (partition : Partition indep.Index),
  ∃ (_ : DecidablePred indep.haltsTruth),
    (∀ m : ℕ,
      ∃ (i : indep.Index) (n : ℕ),
        i ∈ partition.Parts m ∧
        strongEncode (ctx := ctx) (indep := indep)
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) i = C n ∧
        C n ∉ T0)
    ∧ (∀ k : ℕ, Width Truth T0 k)

/-- Constructor: freshness hypothesis implies the full CollatzHasUnboundedWidth statement. -/
theorem collatzHasUnboundedWidth_of_freshness
    {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop) (T0 : Set PropT) (h_T0_sound : ∀ p ∈ T0, Truth p)
    (C : ℕ → PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (indep : InfiniteIndependentHalting Code PropT ctx)
    (partition : Partition indep.Index)
    [DecidablePred indep.haltsTruth]
    (hFreshAll : ∀ m : ℕ, CollatzPartFresh ctx indep partition T0 C
        encode_halt encode_not_halt m) :
    CollatzHasUnboundedWidth ctx Truth T0 C encode_halt encode_not_halt := by
  refine ⟨indep, partition, inferInstance, ?_, ?_⟩
  · -- Freshness part (repackage hFreshAll; simpa guards against future opacity)
    simpa [CollatzPartFresh] using hFreshAll
  · -- Width part (via collatz_unbounded_width)
    exact collatz_unbounded_width (ctx := ctx) (indep := indep) (partition := partition)
      (Truth := Truth) (T0 := T0) (C := C)
      (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
      h_T0_sound h_encode_correct h_encode_correct_neg hFreshAll

/-!
## Architecture Summary

```
CollatzHasUnboundedWidth
         │
         │ (definition = ∃ indep, ∃ partition, ∃ Dec, Freshness ∧ Width)
         │
         ▼
collatzHasUnboundedWidth_of_freshness
         │
         │ (proof: Freshness → Width via collatz_unbounded_width)
         │
         ▼
collatz_unbounded_width
         │
         │ (proof: CollatzPartFresh → PartFresh → Width via Bridge)
         │
         ▼
strong_fresh_implies_unbounded_width (Bridge)
```

The hierarchy `indep → partition → PartFresh → Width` is now encapsulated
in a single testable predicate `CollatzHasUnboundedWidth`.
-/

end RevHalt
