/-
  RevHalt.Dynamics.Core.Laws

  Laws of the axiom graph:
  - Preservation: apply always produces sound nodes (by construction)
  - Strictness: extend with fresh proposition gives strict inclusion
  - Bifurcation: no sound node contains p and Not p
-/

import RevHalt.Dynamics.Core.Move

namespace RevHalt.Dynamics.Core

open Set RevHalt

variable {Code PropT : Type}

namespace Laws

variable {ctx : EnrichedContext Code PropT}

-- ============================================================================
-- Preservation
-- ============================================================================

/-- Preservation is automatic: Move.apply constructs a TheoryNode,
    which guarantees soundness by construction.
    This theorem makes the property explicit. -/
theorem apply_preserves_sound (m : Move ctx) (T : TheoryNode ctx) :
    TheorySound ctx (Move.apply m T).theory :=
  (Move.apply m T).sound

-- ============================================================================
-- Strictness
-- ============================================================================

/-- Extend with a fresh proposition gives strict inclusion. -/
theorem apply_strict_of_fresh (m : Move ctx) (T : TheoryNode ctx)
    (hFresh : m.prop ∉ T) :
    T < Move.apply m T := by
  simp only [TheoryNode.lt_def, Move.apply]
  -- T.theory ⊂ Extend T.theory m.prop
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · exact subset_union_left
  · intro heq
    have hp : m.prop ∈ Extend T.theory m.prop := mem_union_right _ (mem_singleton m.prop)
    rw [← heq] at hp
    exact hFresh hp

/-- Extend_gap with freshness gives strict inclusion. -/
theorem apply_extend_gap_strict_of_fresh (w : GapWitness ctx) (T : TheoryNode ctx)
    (hFresh : GapWitness.prop w ∉ T) :
    T < Move.apply (.extend_gap w) T :=
  apply_strict_of_fresh (.extend_gap w) T hFresh

/-- If T is contained in ProvableSet, then gap witness is fresh and gives strict extension. -/
theorem apply_extend_gap_strict_of_subset_provable (w : GapWitness ctx) (T : TheoryNode ctx)
    (hT : T.theory ⊆ ProvableSet ctx) :
    T < Move.apply (.extend_gap w) T := by
  have hFresh : GapWitness.prop w ∉ T := by
    intro hw
    have : ctx.Provable (GapWitness.prop w) := hT hw
    exact GapWitness.not_provable w this
  exact apply_strict_of_fresh (.extend_gap w) T hFresh

-- ============================================================================
-- Bifurcation
-- ============================================================================

/-- No sound node contains both p and Not p. -/
theorem no_both_p_and_not_p (T : TheoryNode ctx) (p : PropT) :
    ¬ (p ∈ T ∧ ctx.Not p ∈ T) := by
  intro ⟨hp, hnp⟩
  have htp : ctx.Truth p := T.sound p hp
  have htnp : ctx.Truth (ctx.Not p) := T.sound (ctx.Not p) hnp
  have : ¬ ctx.Truth p := (ctx.truth_not_iff p).mp htnp
  exact this htp

/-- No two extensions by p and Not p can both be sound.
    (Already covered by Move.apply constructing sound nodes,
    but this states it in terms of the move perspective.) -/
theorem no_dual_moves (_T : TheoryNode ctx) (p : PropT) (hp : ctx.Truth p) :
    ¬ (ctx.Truth p ∧ ctx.Truth (ctx.Not p)) := by
  intro ⟨_, hNotP⟩
  have : ¬ ctx.Truth p := (ctx.truth_not_iff p).mp hNotP
  exact this hp

/-- Bifurcation for Move.extend: if we extend by p, we cannot extend by Not p
    (the Not p extension would require Truth (Not p), which contradicts Truth p). -/
theorem bifurcation_extend (_T : TheoryNode ctx) (p : PropT) (hp : ctx.Truth p) :
    ¬ ctx.Truth (ctx.Not p) := by
  intro hNotP
  have : ¬ ctx.Truth p := (ctx.truth_not_iff p).mp hNotP
  exact this hp

end Laws

end RevHalt.Dynamics.Core
