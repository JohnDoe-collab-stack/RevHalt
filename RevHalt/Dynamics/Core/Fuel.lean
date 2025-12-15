/-
  RevHalt.Dynamics.Core.Fuel

  T2 as the fuel generator for axiom dynamics.

  Key theorem: from any node T ⊆ ProvableSet, there exists a strict move.

  Preconditions are explicit:
  - fuel_from_T2: T ⊆ ProvableSet → ∃ strict move
  - fuel_from_gap: given GapWitness + freshness → strict move
-/

import RevHalt.Dynamics.Core.Laws

namespace RevHalt.Dynamics.Core

open Set RevHalt

variable {Code PropT : Type}

namespace Fuel

variable {ctx : EnrichedContext Code PropT}

/-- Get a gap witness using classical logic. -/
noncomputable def get_gap_witness (ctx : EnrichedContext Code PropT) : GapWitness ctx :=
  Classical.choice (gapWitness_nonempty ctx)

/-- Fuel from a gap witness: if the gap witness is fresh, we have a strict move. -/
def move_from_gap (w : GapWitness ctx) : Move ctx :=
  .extend_gap w

/-- Fuel theorem (version 1): given a gap witness and freshness, get a strict move. -/
theorem fuel_from_gap (T : TheoryNode ctx) (w : GapWitness ctx)
    (hFresh : GapWitness.prop w ∉ T) :
    T < Move.apply (move_from_gap w) T :=
  Laws.apply_extend_gap_strict_of_fresh w T hFresh

/-- Fuel theorem (version 2): if T ⊆ ProvableSet, any gap witness gives a strict move.
    This is the main "T2 as fuel" theorem.

    Precondition: T.theory ⊆ ProvableSet ctx
    Conclusion: ∃ move, T < apply move T -/
theorem fuel_from_T2 (T : TheoryNode ctx) (hT : T.theory ⊆ ProvableSet ctx) :
    ∃ m : Move ctx, T < Move.apply m T := by
  let w := get_gap_witness ctx
  use move_from_gap w
  exact Laws.apply_extend_gap_strict_of_subset_provable w T hT

/-- Explicit fuel construction: given T ⊆ ProvableSet, construct the move. -/
noncomputable def T2_move (T : TheoryNode ctx) (_ : T.theory ⊆ ProvableSet ctx) : Move ctx :=
  move_from_gap (get_gap_witness ctx)

/-- The T2 move is always strict when precondition holds. -/
theorem T2_move_strict (T : TheoryNode ctx) (hT : T.theory ⊆ ProvableSet ctx) :
    T < Move.apply (T2_move T hT) T := by
  let w := get_gap_witness ctx
  have hFresh : GapWitness.prop w ∉ T := by
    intro hw
    have : ctx.Provable (GapWitness.prop w) := hT hw
    exact GapWitness.not_provable w this
  exact Laws.apply_extend_gap_strict_of_fresh w T hFresh

end Fuel

end RevHalt.Dynamics.Core
