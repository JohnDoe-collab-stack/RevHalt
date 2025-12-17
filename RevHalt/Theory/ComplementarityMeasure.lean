import RevHalt.Theory.Complementarity
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.ComplementarityMeasure

A small “measurement layer” on top of T3-weak and T3-strong.

Goal: make the gap between weak vs strong *measurable* as a branching width.

Key idea:
- Weak gives (at least) one strict sound extension `T1 ⊇ T0`.
- Strong (given a nonempty partition) gives arbitrarily many *pairwise disjoint* “new supports”
  indexed by the partition parts, hence unbounded branching width.

This file stays close to what your T3 already proves; it avoids forcing extra injectivity
on the encoding into `PropT` and measures disjointness at the level of *index support*.
-/

namespace RevHalt

open Set

/-! ## A simple width notion for extensions (weak) -/

section WeakWidth

variable {PropT : Type}
variable (Truth : PropT → Prop)
variable (T0 : Set PropT)

/-- “Strict extension by one new fact”: there exists a sound `T1` extending `T0` with a fresh `p`. -/
def StrictSoundExtension : Prop :=
  ∃ (T1 : Set PropT) (p : PropT),
    T0 ⊆ T1 ∧ (∀ q ∈ T1, Truth q) ∧ p ∈ T1 ∧ p ∉ T0

/-- The (finite) branching width: you can exhibit `n` strict sound extensions. -/
def Width (n : ℕ) : Prop :=
  ∃ (F : Fin n → Set PropT) (w : Fin n → PropT),
    (∀ i, T0 ⊆ F i ∧ (∀ q ∈ F i, Truth q) ∧ w i ∈ F i ∧ w i ∉ T0)

theorem width_one_of_strictSoundExtension (h : StrictSoundExtension (Truth := Truth) (T0 := T0)) :
    Width (Truth := Truth) (T0 := T0) 1 := by
  rcases h with ⟨T1, p, hsub, hsound, hp1, hp0⟩
  refine ⟨(fun _ : Fin 1 => T1), (fun _ : Fin 1 => p), ?_⟩
  intro i
  exact ⟨hsub, hsound, hp1, hp0⟩

end WeakWidth

/-! ## An index-level width notion (strong) -/

section StrongWidth

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)
variable (indep : InfiniteIndependentHalting Code PropT ctx)
variable (partition : Partition indep.Index)

/--
Index-width `n` means: the first `n` partition parts are all nonempty.

This is exactly what you need to *extract n disjoint supports* from the partition.
(Your `Partition` structure currently doesn't require coverage/nonemptiness.)
-/
def IndexWidth (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → ∃ i : indep.Index, i ∈ partition.Parts m

/--
Strong width consequence (packaged):

If you assume nonemptiness for all parts, you get IndexWidth for all finite `n`.
-/
theorem indexWidth_of_allParts_nonempty
    (hNE : ∀ m : ℕ, ∃ i : indep.Index, i ∈ partition.Parts m) :
    ∀ n : ℕ, IndexWidth (ctx := ctx) (indep := indep) (partition := partition) n := by
  intro n m hm
  exact hNE m

/--
A “measured” corollary of your `T3_strong`:

Given
- the hypotheses of `T3_strong` (so the theory family exists),
- and nonemptiness of each part,

we can extract an *arbitrarily large finite family* of pairwise-disjoint supports
(at the index level).

This statement is what strictly separates strong from weak: weak gives at most a
single witnessed extension, while strong gives unboundedly many disjoint supports.
-/
theorem strong_gives_unbounded_indexWidth
    (Truth : PropT → Prop)
    (encode_halt : Code → PropT)
    (encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT)
    (h_T0_sound : ∀ p ∈ T0, Truth p)
    (hNE : ∀ m : ℕ, ∃ i : indep.Index, i ∈ partition.Parts m) :
    (∃ TheoryFamily : ℕ → Set PropT,
        (∀ n, T0 ⊆ TheoryFamily n) ∧
        (∀ n, ∀ p ∈ TheoryFamily n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j))
    ∧ (∀ n : ℕ, IndexWidth (ctx := ctx) (indep := indep) (partition := partition) n) := by
  have hT3 :
      ∃ TheoryFamily : ℕ → Set PropT,
        (∀ n, T0 ⊆ TheoryFamily n) ∧
        (∀ n, ∀ p ∈ TheoryFamily n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j) :=
    T3_strong (ctx := ctx)
      (Truth := Truth)
      (encode_halt := encode_halt)
      (encode_not_halt := encode_not_halt)
      h_encode_correct
      h_encode_correct_neg
      (T0 := T0)
      h_T0_sound
      (indep := indep)
      (partition := partition)

  refine ⟨hT3, ?_⟩
  exact indexWidth_of_allParts_nonempty (ctx := ctx) (indep := indep) (partition := partition) hNE

end StrongWidth

/-! ## Reading the “distance” weak vs strong as a width gap -/

section DistanceSummary

variable {PropT : Type} (Truth : PropT → Prop) (T0 : Set PropT)

/--
A compact “distance” predicate:

- `WeakDistance` means: you have width 1 (at least one strict extension).
- `StrongDistance` means: you have width `n` for all `n` (unbounded branching).

The strong side is stated abstractly; in your development it is provided by
`InfiniteIndependentHalting + Partition + nonemptiness`.
-/
def WeakDistance : Prop := Width (Truth := Truth) (T0 := T0) 1
def StrongDistance : Prop := ∀ n : ℕ, Width (Truth := Truth) (T0 := T0) n

end DistanceSummary

end RevHalt
