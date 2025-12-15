/-
  RevHalt.Dynamics.System

  Unified bundle for Axiom Dynamics.

  - AxiomDynamicsCore: level EnrichedContext
  - AxiomDynamicsOperative: level VerifiableContext (extends Core)
-/

import RevHalt.Dynamics.Core.Node
import RevHalt.Dynamics.Core.Move
import RevHalt.Dynamics.Core.Laws
import RevHalt.Dynamics.Core.Fuel
import RevHalt.Dynamics.Core.Graph
import RevHalt.Dynamics.Core.Path
import RevHalt.Dynamics.Core.Fork
import RevHalt.Dynamics.Operative.Invariant
import RevHalt.Dynamics.Transport.Morphism

namespace RevHalt.Dynamics

open Set

/-! ## Core Axiom Dynamics (EnrichedContext level) -/

/-- The core axiom dynamics structure at the EnrichedContext level.

    Components:
    - Node: theory + soundness certificate
    - Move: monotone operations (extend, extend_gap)
    - Edge: one-step relation
    - Path: explicit move sequences
    - Laws: preservation, strictness, bifurcation
    - Fuel: T2 guarantees strict moves exist
-/
structure AxiomDynamicsCore (Code PropT : Type) where
  ctx : EnrichedContext Code PropT

namespace AxiomDynamicsCore

variable {Code PropT : Type}

/-- The node type. -/
abbrev Node (A : AxiomDynamicsCore Code PropT) := Core.TheoryNode A.ctx

/-- The move type. -/
abbrev Move (A : AxiomDynamicsCore Code PropT) := Core.Move A.ctx

/-- Apply a move to a node. -/
abbrev apply (A : AxiomDynamicsCore Code PropT) := @Core.Move.apply Code PropT A.ctx

/-- Edge relation. -/
abbrev Edge (A : AxiomDynamicsCore Code PropT) := Core.Edge A.ctx

/-- Path type. -/
abbrev Path (A : AxiomDynamicsCore Code PropT) := Core.Path A.ctx

/-- Reachability relation. -/
abbrev Reachable (A : AxiomDynamicsCore Code PropT) := Core.Reachable A.ctx

/-- The empty node. -/
def emptyNode (A : AxiomDynamicsCore Code PropT) : A.Node :=
  Core.TheoryNode.empty A.ctx

/-- Fuel theorem: from any T ⊆ ProvableSet, there exists a strict move. -/
theorem fuel (A : AxiomDynamicsCore Code PropT)
    (T : A.Node) (hT : T.theory ⊆ ProvableSet A.ctx) :
    ∃ m : A.Move, T < A.apply m T :=
  Core.Fuel.fuel_from_T2 T hT

end AxiomDynamicsCore

/-! ## Operative Axiom Dynamics (VerifiableContext level) -/

/-- The operative axiom dynamics structure at the VerifiableContext level.

    Extends Core with:
    - RevLabel: the operative invariant
    - Kit-invariance
    - Connection to Gap, CloK, etc.
-/
structure AxiomDynamicsOperative (Code PropT : Type) extends AxiomDynamicsCore Code PropT where
  vctx : VerifiableContext Code PropT
  h_compat : vctx.toEnrichedContext = ctx

namespace AxiomDynamicsOperative

variable {Code PropT : Type}

/-- The Rev label (operative invariant). -/
def RevLabel (A : AxiomDynamicsOperative Code PropT) (p : PropT) : Prop :=
  Operative.RevLabel A.vctx p

/-- Rev equals Truth. -/
theorem rev_eq_truth (A : AxiomDynamicsOperative Code PropT) (p : PropT) :
    A.RevLabel p ↔ A.vctx.Truth p :=
  Operative.RevLabel.eq_truth p

/-- Rev is kit-invariant. -/
theorem rev_kit_invariant (A : AxiomDynamicsOperative Code PropT)
    (K : RHKit) (hK : DetectsMonotone K) (p : PropT) :
    A.RevLabel p ↔ Rev0_K K (A.vctx.LR ∅ p) :=
  Operative.RevLabel.kit_invariant K hK p

end AxiomDynamicsOperative

end RevHalt.Dynamics
