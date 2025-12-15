/-
  RevHalt.Dynamics.Core.Graph

  Edge relation on theory nodes.
-/

import RevHalt.Dynamics.Core.Move

namespace RevHalt.Dynamics.Core

open Set

variable {Code PropT : Type}

/-- Edge relation: T → T' if there exists a move m with apply m T = T'.
    Note: we use definitional equality on the theory component. -/
def Edge (ctx : EnrichedContext Code PropT) (T T' : TheoryNode ctx) : Prop :=
  ∃ m : Move ctx, (Move.apply m T).theory = T'.theory

namespace Edge

variable {ctx : EnrichedContext Code PropT}

/-- Every move induces an edge. -/
theorem of_move (m : Move ctx) (T : TheoryNode ctx) :
    Edge ctx T (Move.apply m T) :=
  ⟨m, rfl⟩

/-- Edge implies subset (monotonicity of moves). -/
theorem le_of_edge (T T' : TheoryNode ctx) (h : Edge ctx T T') :
    T ≤ T' := by
  obtain ⟨m, heq⟩ := h
  simp only [TheoryNode.le_def]
  calc T.theory ⊆ (Move.apply m T).theory := Move.apply_le m T
    _ = T'.theory := heq

-- Reflexivity is NOT automatic: Edge requires an actual move.
-- Reachability is defined below as reflexive-transitive closure.

/-- Edge transport: if T → U and U = V (theory-wise), then T → V. -/
theorem transport_target {T U V : TheoryNode ctx} (h : Edge ctx T U) (heq : U.theory = V.theory) :
    Edge ctx T V := by
  obtain ⟨m, hm⟩ := h
  use m
  rw [hm, heq]

end Edge

/-- Reachability: reflexive-transitive closure of Edge. -/
def Reachable (ctx : EnrichedContext Code PropT) : TheoryNode ctx → TheoryNode ctx → Prop :=
  Relation.ReflTransGen (Edge ctx)

namespace Reachable

variable {ctx : EnrichedContext Code PropT}

/-- Reflexivity of reachability. -/
theorem refl (T : TheoryNode ctx) : Reachable ctx T T :=
  Relation.ReflTransGen.refl

/-- Transitivity of reachability. -/
theorem trans {T T' T'' : TheoryNode ctx}
    (h₁ : Reachable ctx T T') (h₂ : Reachable ctx T' T'') :
    Reachable ctx T T'' :=
  Relation.ReflTransGen.trans h₁ h₂

/-- One step. -/
theorem single {T T' : TheoryNode ctx} (h : Edge ctx T T') :
    Reachable ctx T T' :=
  Relation.ReflTransGen.single h

/-- Reachable implies subset (monotonicity). -/
theorem le_of_reachable {T T' : TheoryNode ctx} (h : Reachable ctx T T') :
    T ≤ T' := by
  induction h with
  | refl => exact TheoryNode.node_le_refl T
  | tail _ hE ih =>
    exact TheoryNode.node_le_trans ih (Edge.le_of_edge _ _ hE)

end Reachable

end RevHalt.Dynamics.Core
