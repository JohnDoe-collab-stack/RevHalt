import RevHalt
import Mathlib.Data.Set.Basic

namespace RevHalt_Unified

-- ==============================================================================================
-- Part A: T1 - Minimal T1 section
-- ==============================================================================================

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

-- ==============================================================================================
-- Part F: Master Theorem with T1 forced
-- ==============================================================================================

/--
Build EnrichedContext from Rev + ComputabilityModel components.
-/
def EnrichedContext_from_Rev
    {PropT : Type}
    (K : RHKit) (hK : DetectsMonotone K)
    (compile : Code → Trace)
    (Provable : PropT → Prop)
    (FalseT : PropT)
    (Not : PropT → PropT)
    (H : Code → PropT)
    (Truth : PropT → Prop)
    (h_consistent : ¬Provable FalseT)
    (h_absurd : ∀ p, Provable p → Provable (Not p) → Provable FalseT)
    (h_diagonal : ∀ G : Code → PropT, ∃ e, Halts (compile e) ↔ Provable (Not (G e)))
    (h_truth_H : ∀ e, Halts (compile e) ↔ Truth (H e))
    (h_truth_not : ∀ p, Truth (Not p) ↔ ¬Truth p) :
    EnrichedContext Code PropT where
  RealHalts := fun e => Rev0_K K (compile e)  -- T1 forced!
  Provable := Provable
  FalseT := FalseT
  Not := Not
  consistent := h_consistent
  absurd := h_absurd
  diagonal_program := by
    intro G
    obtain ⟨e, he⟩ := h_diagonal G
    use e
    rw [T1_traces K hK (compile e)]
    exact he
  Truth := Truth
  H := H
  h_truth_H := by
    intro e
    rw [T1_traces K hK (compile e)]
    exact h_truth_H e
  truth_not_iff := h_truth_not

/--
**MASTER THEOREM**: Complete T1 → T2 → T3 chain.
-/
theorem RevHalt_Master
    {PropT : Type}
    (K : RHKit) (hK : DetectsMonotone K)
    (compile : Code → Trace)
    (Provable : PropT → Prop)
    (FalseT : PropT)
    (Not : PropT → PropT)
    (H : Code → PropT)
    (Truth : PropT → Prop)
    (h_consistent : ¬Provable FalseT)
    (h_absurd : ∀ p, Provable p → Provable (Not p) → Provable FalseT)
    (h_diagonal : ∀ G : Code → PropT, ∃ e, Halts (compile e) ↔ Provable (Not (G e)))
    (h_truth_H : ∀ e, Halts (compile e) ↔ Truth (H e))
    (h_truth_not : ∀ p, Truth (Not p) ↔ ¬Truth p)
    (h_sound : ∀ p, Provable p → Truth p) :
    let ctx := EnrichedContext_from_Rev K hK compile Provable FalseT Not H Truth
                 h_consistent h_absurd h_diagonal h_truth_H h_truth_not
    -- (1) T1: RealHalts = Halts
    (∀ e, ctx.RealHalts e ↔ Halts (compile e)) ∧
    -- (2) T2: true-but-unprovable exists
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    -- (3) T2': independent code exists (strengthened)
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) ∧
    -- (4) T3: provable set can be strictly extended
    (∃ T1 : Set PropT, ProvableSet ctx ⊂ T1) := by
  let ctx := EnrichedContext_from_Rev K hK compile Provable FalseT Not H Truth
               h_consistent h_absurd h_diagonal h_truth_H h_truth_not
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) T1
    intro e
    exact T1_traces K hK (compile e)
  · -- (2) T2
    exact true_but_unprovable_exists ctx
  · -- (3) T2' strengthened
    exact independent_code_exists ctx h_sound
  · -- (4) T3
    obtain ⟨T1, h_strict, _⟩ := strict_extension ctx
    exact ⟨T1, h_strict⟩

end RevHalt_Unified
