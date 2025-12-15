/-
  RevHalt.Dynamics.Core.Fork

  Fork = bifurcation as an object (not a choice).

  A Fork encodes two conditional branches without requiring a global decision:
  - If you have Truth p, you can build the left node
  - If you have Truth (Not p), you can build the right node
  - Both cannot be sound simultaneously
-/

import RevHalt.Dynamics.Core.Node
import RevHalt.Bridge.ComplementarityAPI

namespace RevHalt.Dynamics.Core

open Set RevHalt

variable {Code PropT : Type}

/--
Fork = bifurcation as an object (without choice):
- pivot p
- two conditional constructors (given a truth certificate)
- exclusion: impossible for both extensions to be sound
-/
structure Fork (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx) where
  pivot : PropT
  mkLeft : ctx.Truth pivot → TheoryNode ctx
  mkRight : ctx.Truth (ctx.Not pivot) → TheoryNode ctx
  exclusion :
    ¬ (TheorySound ctx (Extend T0.theory pivot) ∧
       TheorySound ctx (Extend T0.theory (ctx.Not pivot)))

namespace Fork

variable {ctx : EnrichedContext Code PropT} {T0 : TheoryNode ctx}

/-- Canonical fork on a pivot p (no global hypothesis, no branch choice). -/
def ofPivot (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx) (p : PropT) :
    Fork ctx T0 where
  pivot := p
  mkLeft := fun hp =>
    { theory := Extend T0.theory p
      sound := fun q hq => by
        simp only [mem_Extend_iff] at hq
        rcases hq with hqT0 | rfl
        · exact T0.sound q hqT0
        · exact hp }
  mkRight := fun hnp =>
    { theory := Extend T0.theory (ctx.Not p)
      sound := fun q hq => by
        simp only [mem_Extend_iff] at hq
        rcases hq with hqT0 | rfl
        · exact T0.sound q hqT0
        · exact hnp }
  exclusion := EnrichedContext.not_both_sound_extend_p_and_not (ctx := ctx) (T0 := T0.theory) (p := p)

/-- The left branch of a fork (only constructible with Truth pivot). -/
def left (f : Fork ctx T0) (hp : ctx.Truth f.pivot) : TheoryNode ctx :=
  f.mkLeft hp

/-- The right branch of a fork (only constructible with Truth (Not pivot)). -/
def right (f : Fork ctx T0) (hnp : ctx.Truth (ctx.Not f.pivot)) : TheoryNode ctx :=
  f.mkRight hnp

/-- Fork from ofPivot: left branch extends the base theory. -/
theorem ofPivot_left_extends (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p : PropT) (hp : ctx.Truth p) :
    T0 ≤ (ofPivot ctx T0 p).left hp := by
  simp only [TheoryNode.le_def, left, ofPivot]
  exact subset_union_left

/-- Fork from ofPivot: right branch extends the base theory. -/
theorem ofPivot_right_extends (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p : PropT) (hnp : ctx.Truth (ctx.Not p)) :
    T0 ≤ (ofPivot ctx T0 p).right hnp := by
  simp only [TheoryNode.le_def, right, ofPivot]
  exact subset_union_left

/-- Fork from ofPivot: pivot is in the left branch. -/
theorem ofPivot_pivot_mem_left (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p : PropT) (hp : ctx.Truth p) :
    p ∈ (ofPivot ctx T0 p).left hp := by
  simp only [left, ofPivot, TheoryNode.mem_node_iff, Extend, mem_union, mem_singleton_iff]
  right
  trivial

/-- Fork from ofPivot: Not pivot is in the right branch. -/
theorem ofPivot_not_pivot_mem_right (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p : PropT) (hnp : ctx.Truth (ctx.Not p)) :
    ctx.Not p ∈ (ofPivot ctx T0 p).right hnp := by
  simp only [right, ofPivot, TheoryNode.mem_node_iff, Extend, mem_union, mem_singleton_iff]
  right
  trivial

end Fork

end RevHalt.Dynamics.Core
