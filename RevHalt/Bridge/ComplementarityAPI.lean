import RevHalt.Bridge.Context
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# RevHalt.Bridge.ComplementarityAPI

Local API (T3-style) at the `EnrichedContext` level:
- Soundness of a theory (set of sentences)
- Extension by adding a single axiom
- Sound extension by `GapWitness`
- Strict extension (two variants: explicit freshness or `T0 ⊆ ProvableSet`)
- Disjunction: no sound theory contains both `p` and `Not p`
- Disjunction of extensions: no two sound extensions by `p` and `Not p`
-/

namespace RevHalt

open Set

variable {Code PropT : Type}

/-- Soundness of a theory (set): all its sentences are true. -/
def TheorySound (ctx : EnrichedContext Code PropT) (T : Set PropT) : Prop :=
  ∀ p, p ∈ T → ctx.Truth p

/-- Extension by adding a single axiom. -/
def Extend (T : Set PropT) (p : PropT) : Set PropT := T ∪ {p}

@[simp] theorem mem_Extend_iff {T : Set PropT} {p q : PropT} :
    q ∈ Extend T p ↔ q ∈ T ∨ q = p := by
  rw [Extend, Set.mem_union, Set.mem_singleton_iff]

namespace EnrichedContext

variable (ctx : EnrichedContext Code PropT)
variable {T0 : Set PropT}

-- --------------------------------------------------------------------------------------
-- (1) Sound extension: adding a GapWitness preserves soundness.
-- --------------------------------------------------------------------------------------

theorem extension_sound_of_gapWitness
    (hT0 : TheorySound ctx T0)
    (w : GapWitness ctx) :
    TheorySound ctx (Extend T0 (GapWitness.prop w)) := by
  intro p hp
  rcases (mem_Extend_iff (T := T0) (p := GapWitness.prop w) (q := p)).1 hp with hpT0 | rfl
  · exact hT0 p hpT0
  · exact GapWitness.truth (ctx := ctx) w

-- --------------------------------------------------------------------------------------
-- (2) Strict extension: two variants (freshness hypothesis required).
-- --------------------------------------------------------------------------------------

theorem extension_strict_of_fresh
    (p : PropT)
    (hFresh : p ∉ T0) :
    T0 ⊂ Extend T0 p := by
  refine ⟨subset_union_left, ?_⟩
  intro hSubset
  have hp : p ∈ Extend T0 p := mem_Extend_iff.mpr (Or.inr rfl)
  have hp_T0 : p ∈ T0 := hSubset hp
  exact hFresh hp_T0

theorem extension_strict_of_gapWitness_of_fresh
    (w : GapWitness ctx)
    (hFresh : GapWitness.prop w ∉ T0) :
    T0 ⊂ Extend T0 (GapWitness.prop w) :=
  extension_strict_of_fresh (p := GapWitness.prop w) hFresh

theorem extension_strict_of_gapWitness_of_subset_Provable
    (w : GapWitness ctx)
    (hT0_provable : T0 ⊆ ProvableSet ctx) :
    T0 ⊂ Extend T0 (GapWitness.prop w) := by
  have hFresh : GapWitness.prop w ∉ T0 := by
    intro hw
    have : ctx.Provable (GapWitness.prop w) := hT0_provable hw
    exact (GapWitness.not_provable (ctx := ctx) w) this
  exact extension_strict_of_gapWitness_of_fresh (ctx := ctx) w hFresh

-- --------------------------------------------------------------------------------------
-- (3) Disjunction: a sound theory does not contain both p and Not p.
-- --------------------------------------------------------------------------------------

theorem no_sound_contains_p_and_not_p
    {T : Set PropT}
    (hT : TheorySound ctx T)
    (p : PropT) :
    ¬ (p ∈ T ∧ ctx.Not p ∈ T) := by
  intro h
  have hp  : ctx.Truth p := hT p h.1
  have hnp : ctx.Truth (ctx.Not p) := hT (ctx.Not p) h.2
  have : ¬ ctx.Truth p := (ctx.truth_not_iff p).1 hnp
  exact this hp

-- --------------------------------------------------------------------------------------
-- (4) Disjunction of extensions: no two sound extensions by p and Not p.
-- --------------------------------------------------------------------------------------

theorem not_both_sound_extend_p_and_not
    (p : PropT) :
    ¬ (TheorySound ctx (Extend T0 p) ∧ TheorySound ctx (Extend T0 (ctx.Not p))) := by
  intro h
  have hp_mem : p ∈ Extend T0 p := mem_Extend_iff.mpr (Or.inr rfl)
  have hnp_mem : ctx.Not p ∈ Extend T0 (ctx.Not p) := mem_Extend_iff.mpr (Or.inr rfl)
  have hpT : ctx.Truth p := h.1 p hp_mem
  have hnpT : ctx.Truth (ctx.Not p) := h.2 (ctx.Not p) hnp_mem
  have : ¬ ctx.Truth p := (ctx.truth_not_iff p).1 hnpT
  exact this hpT

theorem not_both_sound_extensions_of_gapWitness
    (w : GapWitness ctx) :
    ¬ (TheorySound ctx (Extend T0 (GapWitness.prop w)) ∧
       TheorySound ctx (Extend T0 (ctx.Not (GapWitness.prop w)))) := by
  -- special case of general disjunction
  simpa using not_both_sound_extend_p_and_not (ctx := ctx) (T0 := T0) (p := GapWitness.prop w)

end EnrichedContext

end RevHalt
