/-
  RevHalt.Dynamics.Core.Node

  TheoryNode: bundled (theory, soundness certificate) pair.

  This is the "node" of the axiom graph at the EnrichedContext level.
-/

import RevHalt.Bridge.Context
import RevHalt.Bridge.ComplementarityAPI
import Mathlib.Data.Set.Basic

namespace RevHalt.Dynamics.Core

open Set

variable {Code PropT : Type}

/-- A theory node is a pair (theory, soundness proof).
    This is the fundamental object of the axiom graph. -/
structure TheoryNode (ctx : EnrichedContext Code PropT) where
  theory : Set PropT
  sound : TheorySound ctx theory

namespace TheoryNode

variable {ctx : EnrichedContext Code PropT}

/-- The empty theory (trivially sound). -/
def empty (ctx : EnrichedContext Code PropT) : TheoryNode ctx where
  theory := ∅
  sound := fun _ h => h.elim

/-- The provable set as a node (requires soundness hypothesis). -/
def fromProvable (ctx : EnrichedContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) : TheoryNode ctx where
  theory := ProvableSet ctx
  sound := fun p hp => h_sound p hp

/-- Subset relation on nodes. -/
def subset (T₁ T₂ : TheoryNode ctx) : Prop :=
  T₁.theory ⊆ T₂.theory

/-- Strict subset relation on nodes. -/
def ssubset (T₁ T₂ : TheoryNode ctx) : Prop :=
  T₁.theory ⊂ T₂.theory

instance : LE (TheoryNode ctx) where
  le := subset

instance : LT (TheoryNode ctx) where
  lt := ssubset

@[simp] theorem le_def (T₁ T₂ : TheoryNode ctx) : T₁ ≤ T₂ ↔ T₁.theory ⊆ T₂.theory := Iff.rfl
@[simp] theorem lt_def (T₁ T₂ : TheoryNode ctx) : T₁ < T₂ ↔ T₁.theory ⊂ T₂.theory := Iff.rfl

/-- Membership in a node. -/
def mem (p : PropT) (T : TheoryNode ctx) : Prop := p ∈ T.theory

instance : Membership PropT (TheoryNode ctx) where
  mem := fun p T => mem p T

@[simp] theorem mem_def (p : PropT) (T : TheoryNode ctx) : p ∈ T ↔ p ∈ T.theory := Iff.rfl

/-- A proposition in a sound node is true. -/
theorem truth_of_mem (T : TheoryNode ctx) (p : PropT) (hp : p ∈ T) : ctx.Truth p :=
  T.sound p hp

end TheoryNode

end RevHalt.Dynamics.Core
