/-
  RevHalt.Examples.ZeroFork

  ═══════════════════════════════════════════════════════════════════════════════
  WHAT THIS DEMONSTRATES (Structure: Local / Two-sided)
  ═══════════════════════════════════════════════════════════════════════════════
  1. FORK = LOCAL TWO-SIDED BIFURCATION without global decision.
  2. Given any pivot p, Fork provides left (Truth p) and right (Truth ¬p) branches.
  3. EXCLUSION: both branches cannot be sound simultaneously.
  4. No Decidable required: certificate carries the branch choice.
  5. Fork.ofPivot: canonical construction for any proposition.
  6. fork_navigate_left/right: navigate with truth certificate → Edge.
  7. Demonstrates T3 "local power": extend without uniform decider.
  8. Integrates with Graph/Path: edges from Fork feed into Path.
  9. Applicable to any RefSystem: Cut 0, Bit n a, etc.
  10. Key insight: two-sided ≠ decision; it's certificate-carried branching.
  ═══════════════════════════════════════════════════════════════════════════════
-/

import RevHalt.Dynamics.Core.Fork
import RevHalt.Dynamics.Core.RefSystem

namespace RevHalt.Examples

open RevHalt
open RevHalt.Dynamics.Core

/-!
## Zero Fork Demo

Given a RefSystem, we can construct a Fork on any Cut sentence.
This demonstrates two-sided complementarity at the RefSystem level.
-/

variable {Code PropT : Type}
variable (ctx : EnrichedContext Code PropT)

/-- Given a pivot p (e.g., Cut q x encoded as a PropT), we can build a Fork.
    The Fork structure captures:
    - left branch: Truth p → TheoryNode
    - right branch: Truth (Not p) → TheoryNode
    - exclusion: not both sound
-/
theorem fork_on_any_pivot
    (T0 : TheoryNode ctx) (p : PropT) :
    ∃ (f : Fork ctx T0), f.pivot = p :=
  ⟨Fork.ofPivot ctx T0 p, rfl⟩

/-- Fork exclusion: both branches cannot be sound simultaneously. -/
theorem fork_exclusion_principle
    (T0 : TheoryNode ctx) (p : PropT) :
    ¬ (TheorySound ctx (Extend T0.theory p) ∧
       TheorySound ctx (Extend T0.theory (ctx.Not p))) :=
  (Fork.ofPivot ctx T0 p).exclusion

/-- With a truth certificate, we can navigate to one branch. -/
theorem fork_navigate_left
    (T0 : TheoryNode ctx) (p : PropT) (hp : ctx.Truth p) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ p ∈ T1.theory := by
  let f := Fork.ofPivot ctx T0 p
  let T1 := f.left hp
  refine ⟨T1, Fork.ofPivot_edge_left ctx T0 p hp, ?_⟩
  exact Fork.ofPivot_pivot_mem_left ctx T0 p hp

theorem fork_navigate_right
    (T0 : TheoryNode ctx) (p : PropT) (hnp : ctx.Truth (ctx.Not p)) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ ctx.Not p ∈ T1.theory := by
  let f := Fork.ofPivot ctx T0 p
  let T1 := f.right hnp
  refine ⟨T1, Fork.ofPivot_edge_right ctx T0 p hnp, ?_⟩
  exact Fork.ofPivot_not_pivot_mem_right ctx T0 p hnp

/-!
## Key point

Fork demonstrates the two-sided complementarity mechanism:
- No global decision (no Decidable)
- Certificate carries the branch
- Exclusion is built-in
- Directly usable in Graph/Path
-/

end RevHalt.Examples
