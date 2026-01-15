import RevHalt.Theory.TheoryDynamics_Transfinite

/-!
# RevHalt.Theory.TheoryDynamics_Transfinite_Jump

Limit operators with explicit "jump" content at limits.
This isolates the novelty injection semantics from the core transfinite dynamics.
-/

namespace RevHalt

open Set
open Ordinal

section JumpLimit

universe u v

variable {PropT : Type u}

/-- Prelimit aggregate (union over stages). -/
def preLimit {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) : Set PropT :=
  transUnionFamily (α := alpha) chain

/--
Limit operator built from a prelimit aggregate, a jump `J`, and a closure `Cn`.
This models "novel content injection" at limits.
-/
def jumpLimitOp (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT) : LimitOp PropT :=
  { apply := fun {alpha} chain =>
      let U := preLimit (PropT := PropT) (alpha := alpha) chain
      Cn (U ∪ J U) }

/-- There exists a genuine novelty injected by `J`. -/
def InjectsNew (J : Set PropT → Set PropT) : Prop :=
  ∃ U, ∃ p, p ∈ J U ∧ p ∉ U

/-- `J` strictly extends every `U` (no idempotent collapse). -/
def StrictlyExtends (J : Set PropT → Set PropT) : Prop :=
  ∀ U, U ⊆ U ∪ J U ∧ ¬ U ∪ J U ⊆ U

/--
There is an element injected only at the limit, not at any stage.
This is a sharp emergence condition for the jump `J`.
-/
def JumpDiscontinuous (J : Set PropT → Set PropT) : Prop :=
  ∃ (alpha : Ordinal.{v}) (chain : ∀ beta < alpha, Set PropT),
    let U := preLimit (PropT := PropT) (alpha := alpha) chain
    ∃ p, p ∈ J U ∧ (∀ beta (h : beta < alpha), p ∉ J (chain beta h))

end JumpLimit

end RevHalt
