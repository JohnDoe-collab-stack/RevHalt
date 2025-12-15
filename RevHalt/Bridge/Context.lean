import RevHalt.Theory
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Bridge.Context

EnrichedContext and related context structures.

## Contents
- `EnrichedContext`: Context with classical Truth
- `ProvableSet`: Set of provable propositions
- `true_but_unprovable_exists`: T2 consequence
- `independent_code_exists`: Strengthened T2
-/

namespace RevHalt

variable {Code : Type}

/-- RealHalts defined via Rev0_K. T1 connection is via T1_traces. -/
abbrev RealHalts_via_Rev (K : RHKit) (compile : Code → Trace) (e : Code) : Prop :=
  Rev0_K K (compile e)

-- ==============================================================================================
-- Part B: Use T2 to show incompleteness
-- ==============================================================================================

/--
**Key Theorem**: T2_impossibility prevents any total+correct+complete encoding.
-/
theorem encoding_cannot_be_complete
    {PropT : Type}
    (ctx : TuringGodelContext' Code PropT)
    (H : Code → PropT)
    (h_total : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e)))
    (h_correct : ∀ e, ctx.RealHalts e → ctx.Provable (H e))
    (h_complete : ∀ e, ¬ctx.RealHalts e → ctx.Provable (ctx.Not (H e))) :
    False := by
  have h : ∃ _ : InternalHaltingPredicate ctx, True := ⟨⟨H, h_total, h_correct, h_complete⟩, trivial⟩
  exact T2_impossibility ctx h

/--
**Corollary**: For any halting predicate H, there exists an undecided code.
-/
theorem undecidable_code_exists
    {PropT : Type}
    (ctx : TuringGodelContext' Code PropT)
    (H : Code → PropT) :
    ∃ e, (ctx.RealHalts e ∧ ¬ctx.Provable (H e)) ∨
         (¬ctx.RealHalts e ∧ ¬ctx.Provable (ctx.Not (H e))) := by
  by_contra h_contra
  push_neg at h_contra
  apply encoding_cannot_be_complete ctx H
  · intro e
    by_cases h : ctx.RealHalts e
    · left; exact (h_contra e).1 h
    · right; exact (h_contra e).2 h
  · intro e hReal; exact (h_contra e).1 hReal
  · intro e hNotReal; exact (h_contra e).2 hNotReal

-- ==============================================================================================
-- Part C: Enriched Context with classical Truth
-- ==============================================================================================

/--
Enriched context with classical truth.
-/
structure EnrichedContext (Code PropT : Type) extends TuringGodelContext' Code PropT where
  Truth : PropT → Prop
  H : Code → PropT  -- halting predicate
  h_truth_H : ∀ e, RealHalts e ↔ Truth (H e)
  truth_not_iff : ∀ p, Truth (Not p) ↔ ¬Truth p

attribute [simp] EnrichedContext.truth_not_iff

/-- Simp lemma wrapper for truth_not_iff to ensure it triggers easily on the context. -/
@[simp] theorem truth_not_simp (ctx : EnrichedContext Code PropT) (p : PropT) :
    ctx.Truth (ctx.Not p) ↔ ¬ctx.Truth p :=
  ctx.truth_not_iff p

/-- Derive h_truth_not from truth_not_iff. -/
theorem EnrichedContext.h_truth_not (ctx : EnrichedContext Code PropT) :
    ∀ e, ¬ctx.RealHalts e → ctx.Truth (ctx.Not (ctx.H e)) := by
  intro e hNotReal
  rw [ctx.truth_not_iff]
  intro h
  exact hNotReal (ctx.h_truth_H e |>.mpr h)

/--
Extract true-but-unprovable from the gap.
-/
theorem true_but_unprovable_exists (ctx : EnrichedContext Code PropT) :
    ∃ p : PropT, ctx.Truth p ∧ ¬ctx.Provable p := by
  obtain ⟨e, h_gap⟩ := undecidable_code_exists ctx.toTuringGodelContext' ctx.H
  rcases h_gap with ⟨hReal, hNotProv⟩ | ⟨hNotReal, hNotProvNeg⟩
  · exact ⟨ctx.H e, ctx.h_truth_H e |>.mp hReal, hNotProv⟩
  · exact ⟨ctx.Not (ctx.H e), ctx.h_truth_not e hNotReal, hNotProvNeg⟩

/--
**GapWitness**: A typed witness for true-but-unprovable propositions.

Encapsulates the indetermination (H e vs Not (H e)) as a local object.
All downstream reasoning is parameterized by this witness.
-/
def GapWitness (ctx : EnrichedContext Code PropT) : Type :=
  { p : PropT // ctx.Truth p ∧ ¬ctx.Provable p }

/--
**Gap witnesses exist** (via T2).
-/
theorem gapWitness_nonempty (ctx : EnrichedContext Code PropT) :
    Nonempty (GapWitness ctx) := by
  obtain ⟨p, hpT, hpNP⟩ := true_but_unprovable_exists ctx
  exact ⟨⟨p, hpT, hpNP⟩⟩

/-- Extract the proposition from a gap witness. -/
def GapWitness.prop {ctx : EnrichedContext Code PropT} (w : GapWitness ctx) : PropT := w.1

/-- A gap witness is true. -/
theorem GapWitness.truth {ctx : EnrichedContext Code PropT} (w : GapWitness ctx) :
    ctx.Truth w.prop := w.2.1

/-- A gap witness is not provable. -/
theorem GapWitness.not_provable {ctx : EnrichedContext Code PropT} (w : GapWitness ctx) :
    ¬ctx.Provable w.prop := w.2.2

-- ==============================================================================================
-- Part D: Strengthen to true undecidability
-- ==============================================================================================

/--
If Provable is sound (Provable p → Truth p), then the gap becomes:
- ¬Provable(H e) ∧ ¬Provable(Not(H e))
-/
theorem independent_code_exists
    (ctx : EnrichedContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e)) := by
  obtain ⟨e, h_gap⟩ := undecidable_code_exists ctx.toTuringGodelContext' ctx.H
  use e
  rcases h_gap with ⟨hReal, hNotProv⟩ | ⟨hNotReal, hNotProvNeg⟩
  · -- Case: RealHalts e ∧ ¬Provable(H e)
    constructor
    · exact hNotProv
    · intro hProv
      -- Provable(Not(H e)) → Truth(Not(H e)) → ¬Truth(H e) → ¬RealHalts e
      have h1 : ctx.Truth (ctx.Not (ctx.H e)) := h_sound _ hProv
      have h2 : ¬ctx.Truth (ctx.H e) := ctx.truth_not_iff (ctx.H e) |>.mp h1
      have h3 : ¬ctx.RealHalts e := fun h => h2 (ctx.h_truth_H e |>.mp h)
      exact h3 hReal
  · -- Case: ¬RealHalts e ∧ ¬Provable(Not(H e))
    constructor
    · intro hProv
      -- Provable(H e) → Truth(H e) → RealHalts e
      have h1 : ctx.Truth (ctx.H e) := h_sound _ hProv
      have h2 : ctx.RealHalts e := ctx.h_truth_H e |>.mpr h1
      exact hNotReal h2
    · exact hNotProvNeg

-- ==============================================================================================
-- Part E: T3 extension
-- ==============================================================================================

/-- T0 is defined as the provable set. -/
def ProvableSet (ctx : EnrichedContext Code PropT) : Set PropT :=
  {p | ctx.Provable p}

/-- If Provable is sound, ProvableSet is a subset of truths. -/
theorem ProvableSet_sound (ctx : EnrichedContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∀ p ∈ ProvableSet ctx, ctx.Truth p := by
  intro p hp
  exact h_sound p hp

/-- Strict extension: The provable set can always be extended with a true unprovable. -/
theorem strict_extension (ctx : EnrichedContext Code PropT) :
    ∃ T1 : Set PropT, ProvableSet ctx ⊂ T1 ∧ (∃ p ∈ T1, ctx.Truth p ∧ ¬ctx.Provable p) := by
  obtain ⟨p, h_true, h_not_prov⟩ := true_but_unprovable_exists ctx
  have h_fresh : p ∉ ProvableSet ctx := h_not_prov
  use ProvableSet ctx ∪ {p}
  constructor
  · constructor
    · exact Set.subset_union_left
    · intro h_eq
      exact h_fresh (h_eq (Set.mem_union_right (ProvableSet ctx) rfl))
  · exact ⟨p, Set.mem_union_right _ rfl, h_true, h_not_prov⟩

/-- Alternative: extend any sound theory. -/
theorem strict_extension' (ctx : EnrichedContext Code PropT)
    (T0 : Set PropT)
    (h_T0_provable : T0 ⊆ ProvableSet ctx)
    (h_T0_sound : ∀ p ∈ T0, ctx.Truth p) :
    ∃ T1 : Set PropT, T0 ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p) := by
  obtain ⟨p, h_true, h_not_prov⟩ := true_but_unprovable_exists ctx
  have h_fresh : p ∉ T0 := fun h => h_not_prov (h_T0_provable h)
  use T0 ∪ {p}
  constructor
  · constructor
    · exact Set.subset_union_left
    · intro h_eq; exact h_fresh (h_eq (Set.mem_union_right T0 rfl))
  · intro q hq
    rcases hq with h_in | h_eq
    · exact h_T0_sound q h_in
    · rw [h_eq]; exact h_true

end RevHalt
