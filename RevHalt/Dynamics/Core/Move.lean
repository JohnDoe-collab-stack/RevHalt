/-
  RevHalt.Dynamics.Core.Move

  Move: operations on theory nodes.

  Phase 1: Only monotone moves (extend, extend_gap).
  `restrict` deferred to later phase.
-/

import RevHalt.Dynamics.Core.Node

namespace RevHalt.Dynamics.Core

open Set

variable {Code PropT : Type}

/-- A move in the axiom graph.
    Phase 1: only monotone moves (extension).
    - `extend p hp`: add proposition p with truth proof
    - `extend_gap w`: add gap witness proposition -/
inductive Move (ctx : EnrichedContext Code PropT) where
  | extend (p : PropT) (hp : ctx.Truth p) : Move ctx
  | extend_gap (w : GapWitness ctx) : Move ctx

namespace Move

variable {ctx : EnrichedContext Code PropT}

/-- The proposition added by a move. -/
def prop : Move ctx → PropT
  | .extend p _ => p
  | .extend_gap w => GapWitness.prop w

/-- The truth proof for the proposition added. -/
def truth_proof (m : Move ctx) : ctx.Truth m.prop := by
  cases m with
  | extend p hp => exact hp
  | extend_gap w => exact GapWitness.truth w

/-- Apply a move to a theory node, producing a new theory node.
    This is a total function: moves always produce valid nodes. -/
def apply (m : Move ctx) (T : TheoryNode ctx) : TheoryNode ctx where
  theory := Extend T.theory m.prop
  sound := by
    intro q hq
    simp only [Extend, mem_union, mem_singleton_iff] at hq
    rcases hq with hqT | rfl
    · exact T.sound q hqT
    · exact m.truth_proof

/-- Apply is always an extension (monotone). -/
theorem apply_le (m : Move ctx) (T : TheoryNode ctx) :
    T ≤ apply m T := by
  simp only [TheoryNode.le_def, apply]
  exact subset_union_left

/-- The new proposition is in the result. -/
theorem prop_mem_apply (m : Move ctx) (T : TheoryNode ctx) :
    m.prop ∈ apply m T := by
  simp only [TheoryNode.mem_node_iff, apply, Extend, mem_union, mem_singleton_iff]
  right
  trivial

end Move

end RevHalt.Dynamics.Core
