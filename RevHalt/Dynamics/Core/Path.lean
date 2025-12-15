/-
  RevHalt.Dynamics.Core.Path

  Path: explicit sequence of moves between nodes.

  This is a general structure, not equivalent to Chain.
  Chain will embed into Path as a special case.
-/

import RevHalt.Dynamics.Core.Graph
import Mathlib.Tactic.Ring

namespace RevHalt.Dynamics.Core

open Set

variable {Code PropT : Type}

/-- A path from T to T' is an explicit sequence of moves.
    Inductive definition: nil (identity) or step (one move + path from result). -/
inductive Path (ctx : EnrichedContext Code PropT) : TheoryNode ctx → TheoryNode ctx → Type where
  | nil : (T : TheoryNode ctx) → Path ctx T T
  | step : (m : Move ctx) → (T : TheoryNode ctx) →
           Path ctx (Move.apply m T) T' → Path ctx T T'

namespace Path

variable {ctx : EnrichedContext Code PropT}

/-- Length of a path. -/
def length : Path ctx T T' → ℕ
  | .nil _ => 0
  | .step _ _ p => p.length + 1

/-- Concatenation of paths. -/
def concat : Path ctx T T' → Path ctx T' T'' → Path ctx T T''
  | .nil _, q => q
  | .step m T p, q => .step m T (p.concat q)

/-- Length of concatenation is sum of lengths. -/
theorem length_concat (p : Path ctx T T') (q : Path ctx T' T'') :
    (p.concat q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [concat, length]
  | step m T p ih =>
    simp only [concat, length]
    rw [ih]
    omega

/-- Path induces reachability. -/
theorem reachable_of_path : Path ctx T T' → Reachable ctx T T'
  | .nil _ => Reachable.refl _
  | .step m T p => by
    apply Reachable.trans
    · exact Reachable.single (Edge.of_move m T)
    · exact reachable_of_path p

/-- Path from a single move. -/
def of_move (m : Move ctx) (T : TheoryNode ctx) : Path ctx T (Move.apply m T) :=
  .step m T (.nil _)

/-- Length of single-move path is 1. -/
@[simp] theorem length_of_move (m : Move ctx) (T : TheoryNode ctx) :
    (of_move m T).length = 1 := rfl

/-- The empty path has length 0. -/
@[simp] theorem length_nil (T : TheoryNode ctx) : (Path.nil T).length = 0 := rfl

/-- Path preserves monotonicity: start ≤ end. -/
theorem le_of_path : Path ctx T T' → T ≤ T'
  | .nil _ => TheoryNode.node_le_refl _
  | .step m T p => TheoryNode.node_le_trans (Move.apply_le m T) (le_of_path p)

end Path

end RevHalt.Dynamics.Core
