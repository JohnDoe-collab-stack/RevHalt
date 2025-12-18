import RevHalt.Theory.Complementarity
import RevHalt.Theory.ComplementarityMeasure
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.ComplementarityMeasureBridge

Strengthens the measurement layer by **linking**:
- index-level width (`IndexWidth`) coming from partitions (T3-strong infrastructure),
to
- proposition-level branching width (`Width`) used to quantify complementary extensions.

Key point:
`T3_strong` (as currently stated) returns existence of a theory family but does not expose
membership facts like "encode(i) ∈ TheoryFamily(n)". To bridge *without changing*
`Complementarity.lean`, we reintroduce the explicit constructed family used in the proof of
`T3_strong` and prove the missing link.

This yields a clean, checkable theorem:
if each partition part contains a **fresh** encoded proposition not already in `T0`,
then `Width n` holds for all `n`.
-/

namespace RevHalt

open Set

/-- Partition from an injection `f : ℕ → Index`: Parts m = {f m}. -/
def partitionOfNatInjection {Index : Type} (f : ℕ → Index) (inj : Function.Injective f) :
    Partition Index where
  Parts := fun m => {f m}
  disjoint := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro x hx hx'
    have hx1 : x = f n := by simpa [Set.mem_singleton_iff] using hx
    have hx2 : x = f m := by simpa [Set.mem_singleton_iff] using hx'
    have hfm : f n = f m := hx1.symm.trans hx2
    exact hnm (inj hfm)

section StrongToWidth

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)
variable (indep : InfiniteIndependentHalting Code PropT ctx)
variable (partition : Partition indep.Index)
variable [∀ i, Decidable (indep.haltsTruth i)]

/-- Encode a halting status as a proposition.
    Uses the meta-level halting truth to choose the appropriate encoding. -/
def strongEncode (encode_halt encode_not_halt : Code → PropT) (i : indep.Index) : PropT :=
  if indep.haltsTruth i then encode_halt (indep.family i)
  else encode_not_halt (indep.family i)

/-- The explicit family used in the proof of `T3_strong`. -/
def strongTheoryFamily (encode_halt encode_not_halt : Code → PropT) (T0 : Set PropT) (n : ℕ) :
    Set PropT :=
  T0 ∪ { p | ∃ i ∈ partition.Parts n, p = strongEncode ctx indep encode_halt encode_not_halt i }

/-- `T0 ⊆ strongTheoryFamily n`. -/
theorem strongTheoryFamily_extends (encode_halt encode_not_halt : Code → PropT)
    (T0 : Set PropT) (n : ℕ) :
    T0 ⊆ strongTheoryFamily ctx indep partition encode_halt encode_not_halt T0 n :=
  fun _ hp => Or.inl hp

/-- Soundness of `strongTheoryFamily`. -/
theorem strongTheoryFamily_sound (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT) (h_T0_sound : ∀ p ∈ T0, Truth p) (n : ℕ) :
    ∀ p ∈ strongTheoryFamily ctx indep partition encode_halt encode_not_halt T0 n, Truth p := by
  intro p hp
  rcases hp with hT0 | ⟨i, _hi, heq⟩
  · exact h_T0_sound p hT0
  · rw [heq]
    show Truth (strongEncode ctx indep encode_halt encode_not_halt i)
    simp only [strongEncode]
    by_cases hht : indep.haltsTruth i
    · simp only [if_pos hht]
      have hreal : ctx.RealHalts (indep.family i) := (indep.halts_agree i).2 hht
      exact h_encode_correct (indep.family i) hreal
    · simp only [if_neg hht]
      have hnot : ¬ ctx.RealHalts (indep.family i) := fun hreal =>
        hht ((indep.halts_agree i).1 hreal)
      exact h_encode_correct_neg (indep.family i) hnot

/-- Membership: if `i ∈ Parts n`, then `strongEncode i ∈ strongTheoryFamily n`. -/
theorem strongEncode_mem_family (encode_halt encode_not_halt : Code → PropT)
    (T0 : Set PropT) {n : ℕ} {i : indep.Index} (hi : i ∈ partition.Parts n) :
    strongEncode ctx indep encode_halt encode_not_halt i ∈
        strongTheoryFamily ctx indep partition encode_halt encode_not_halt T0 n :=
  Or.inr ⟨i, hi, rfl⟩

/-!
### The key bridge: IndexWidth + freshness ⇒ Width

Freshness is exactly the missing condition to make the extensions *strict* (new information).
Without it, an encoded proposition could already belong to `T0`, so `Width` (as "strict") would
not follow.
-/

/-- Freshness at part `m`: there exists an index in the part whose encoded proposition is not in `T0`. -/
def PartFresh (encode_halt encode_not_halt : Code → PropT) (T0 : Set PropT) (m : ℕ) : Prop :=
  ∃ i : indep.Index, i ∈ partition.Parts m ∧
    strongEncode ctx indep encode_halt encode_not_halt i ∉ T0

/-- If every part up to `n-1` is fresh, we get proposition-level `Width n`. -/
theorem width_of_fresh_parts (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT) (h_T0_sound : ∀ p ∈ T0, Truth p) (n : ℕ)
    (hFresh : ∀ m : ℕ, m < n → PartFresh ctx indep partition encode_halt encode_not_halt T0 m) :
    Width Truth T0 n := by
  classical
  -- Choose one fresh index per part m < n
  choose! pick hpick_mem hpick_fresh using hFresh

  let F : Fin n → Set PropT := fun i =>
    strongTheoryFamily ctx indep partition encode_halt encode_not_halt T0 i.1

  let w : Fin n → PropT := fun i =>
    strongEncode ctx indep encode_halt encode_not_halt (pick i.1 i.2)

  refine ⟨F, w, fun i => ?_⟩
  constructor
  · exact strongTheoryFamily_extends ctx indep partition encode_halt encode_not_halt T0 i.1
  constructor
  · exact strongTheoryFamily_sound ctx indep partition Truth encode_halt encode_not_halt
      h_encode_correct h_encode_correct_neg T0 h_T0_sound i.1
  constructor
  · exact strongEncode_mem_family ctx indep partition encode_halt encode_not_halt T0
      (hpick_mem i.1 i.2)
  · exact hpick_fresh i.1 i.2

/--
Unbounded branching width (proposition-level) from the strong infrastructure + freshness.

This is the clean quantitative "distance":
weak can witness `Width 1`, while strong+fresh yields `∀ n, Width n`.
-/
theorem strong_fresh_implies_unbounded_width (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT) (h_T0_sound : ∀ p ∈ T0, Truth p)
    (hFreshAll : ∀ m : ℕ, PartFresh ctx indep partition encode_halt encode_not_halt T0 m) :
    ∀ n : ℕ, Width Truth T0 n := fun n =>
  width_of_fresh_parts ctx indep partition Truth encode_halt encode_not_halt
    h_encode_correct h_encode_correct_neg T0 h_T0_sound n (fun m _ => hFreshAll m)



/-- Freshness simplifies for `Parts m = {f m}`. -/
theorem partFresh_partitionOfNatInjection_iff
    (encode_halt encode_not_halt : Code → PropT)
    (T0 : Set PropT)
    (f : ℕ → indep.Index) (hf : Function.Injective f)
    (m : ℕ) :
    PartFresh (ctx := ctx) (indep := indep)
      (partition := partitionOfNatInjection f hf)
      (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
      T0 m
    ↔
    strongEncode (ctx := ctx) (indep := indep)
      (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) (f m) ∉ T0 := by
  constructor
  · rintro ⟨i, hi, hfresh⟩
    have : i = f m := by
      simpa [partitionOfNatInjection, Set.mem_singleton_iff] using hi
    simpa [this] using hfresh
  · intro hfresh
    refine ⟨f m, ?_, hfresh⟩
    simp [partitionOfNatInjection]

/--
  Freshness via branch unprovability (Refined Reduction).
  To show `strongEncode` is not in `T0` (assuming `T0 ⊆ Provable`), we only need to show
  that the *true* branch is unprovable. We don't need to assume unprovability of the false branch.
-/
theorem freshness_via_branch_unprovable
    (encode_halt encode_not_halt : Code → PropT)
    (T0 : Set PropT)
    (h_T0_sub_Provable : ∀ p ∈ T0, ctx.Provable p)
    (h_not_provable_halt : ∀ i, indep.haltsTruth i →
        ¬ ctx.Provable (encode_halt (indep.family i)))
    (h_not_provable_not_halt : ∀ i, ¬ indep.haltsTruth i →
        ¬ ctx.Provable (encode_not_halt (indep.family i)))
    (i : indep.Index) :
    strongEncode ctx indep encode_halt encode_not_halt i ∉ T0 := by
  intro h_in_T0
  have h_prov := h_T0_sub_Provable _ h_in_T0
  dsimp [strongEncode] at h_prov
  by_cases hht : indep.haltsTruth i
  · simp [hht] at h_prov
    exact (h_not_provable_halt i hht) h_prov
  · simp [hht] at h_prov
    exact (h_not_provable_not_halt i hht) h_prov

end StrongToWidth

end RevHalt
