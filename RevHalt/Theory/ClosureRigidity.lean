/-
  RevHalt.Theory.ClosureRigidity

  Abstract theorem: unique extension along a closure operator.

  This module extracts the pattern behind T1 (Canonicity):
  - A closure operator C on observations
  - A predicate P correct on fixed points of C
  - Conclusion: P ∘ C is the unique extension of P|_{Fix(C)} to all observations

  T1 is an instance of this pattern with:
  - Observations = Trace
  - Closure = up
  - Predicate = K.Proj
  - Correctness on Fix(C) = DetectsMonotone
-/

import RevHalt.Base.Trace
import RevHalt.Base.Kit

namespace RevHalt.Theory

open Set

/-!
## Abstract Closure Rigidity

Given:
- An observation space X
- A closure function cl : X → X (extensive for Halts-equivalent, idempotent)
- A reference predicate R : X → Prop (the "ground truth")
- A test predicate P : X → Prop

If P agrees with R on the image of cl (the "closed" observations),
then P ∘ cl agrees with R on all observations.
-/

section Abstract

variable {X : Type*}

/-- A closure-like operator with respect to an observable predicate.
    We don't require a full order structure, just:
    - idempotent: cl (cl x) = cl x
    - observable_eq: observable (cl x) ↔ observable x
    The "extensive" property is captured by observable_eq. -/
structure ObservationClosure (X : Type*) (observable : X → Prop) where
  cl : X → X
  idempotent : ∀ x, cl (cl x) = cl x
  observable_eq : ∀ x, observable (cl x) ↔ observable x

variable {observable : X → Prop}

/-- P agrees with observable on closed elements. -/
def AgreesOnClosed (C : ObservationClosure X observable) (P : X → Prop) : Prop :=
  ∀ x, P (C.cl x) ↔ observable (C.cl x)

/-- Main theorem: if P agrees with observable on closed, then P ∘ cl ↔ observable. -/
theorem unique_extension_along_closure
    (C : ObservationClosure X observable) (P : X → Prop)
    (h : AgreesOnClosed C P) :
    ∀ x, P (C.cl x) ↔ observable x := by
  intro x
  have hAgree := h x
  have hObs := C.observable_eq x
  exact hAgree.trans hObs

/-- Corollary: two predicates that agree on closed give the same verdict. -/
theorem closure_rigidity_uniqueness
    (C : ObservationClosure X observable) (P₁ P₂ : X → Prop)
    (h₁ : AgreesOnClosed C P₁)
    (h₂ : AgreesOnClosed C P₂) :
    ∀ x, P₁ (C.cl x) ↔ P₂ (C.cl x) := by
  intro x
  have hL : P₁ (C.cl x) ↔ observable x := unique_extension_along_closure C P₁ h₁ x
  have hR : P₂ (C.cl x) ↔ observable x := unique_extension_along_closure C P₂ h₂ x
  exact hL.trans hR.symm

end Abstract

/-!
## T1 as an Instance

We show that T1 (Canonicity) is exactly this pattern applied to:
- X = Trace
- cl = up
- observable = Halts
- P = K.Proj
- AgreesOnClosed = DetectsMonotone (restricted to monotone traces)
-/

/-- The `up` operator forms an observation closure with Halts as observable. -/
def upClosure : ObservationClosure Trace Halts where
  cl := up
  idempotent := fun T => by
    funext n
    apply propext
    constructor
    · rintro ⟨k, hk, ⟨j, hj, hTj⟩⟩
      exact ⟨j, Nat.le_trans hj hk, hTj⟩
    · rintro ⟨k, hk, hTk⟩
      exact ⟨k, hk, ⟨k, Nat.le_refl k, hTk⟩⟩
  observable_eq := exists_up_iff

/-- DetectsMonotone implies AgreesOnClosed for upClosure.
    (The key insight: up T is always monotone, so DetectsMonotone applies.) -/
theorem detectsMonotone_implies_agreesOnClosed (K : RHKit) (hK : DetectsMonotone K) :
    AgreesOnClosed upClosure K.Proj := by
  intro T
  have hMono : Monotone (up T) := up_mono T
  exact hK (up T) hMono

/-- T1_traces is an instance of unique_extension_along_closure. -/
theorem T1_as_closure_rigidity (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    K.Proj (up T) ↔ Halts T :=
  unique_extension_along_closure upClosure K.Proj
    (detectsMonotone_implies_agreesOnClosed K hK) T

/-- T1_uniqueness is an instance of closure_rigidity_uniqueness. -/
theorem T1_uniqueness_as_closure_rigidity
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) (T : Trace) :
    K₁.Proj (up T) ↔ K₂.Proj (up T) :=
  closure_rigidity_uniqueness upClosure K₁.Proj K₂.Proj
    (detectsMonotone_implies_agreesOnClosed K₁ h₁)
    (detectsMonotone_implies_agreesOnClosed K₂ h₂) T

/-!
## Instance 2: DR1 Kit-Invariance (abstract)

Any two predicates that agree on closed traces give the same verdict.
This is the abstract pattern behind DR1_ref in RefSystem.
-/

/-- Abstract DR1: two predicates agreeing on closed give same verdict. -/
theorem abstract_DR1
    (P₁ P₂ : Trace → Prop)
    (h₁ : ∀ T, P₁ (up T) ↔ Halts (up T))
    (h₂ : ∀ T, P₂ (up T) ↔ Halts (up T)) :
    ∀ T, P₁ (up T) ↔ P₂ (up T) := by
  intro T
  have hL : P₁ (up T) ↔ Halts T := (h₁ T).trans (upClosure.observable_eq T)
  have hR : P₂ (up T) ↔ Halts T := (h₂ T).trans (upClosure.observable_eq T)
  exact hL.trans hR.symm

/-!
## Instance 3: Generic Closure Schema (parameterized)

Any closure operator with observable-preserving property yields uniqueness.
-/

/-- Abstract pattern: given any such closure, uniqueness follows. -/
theorem generic_closure_uniqueness
    {X : Type*} {observable : X → Prop}
    (C : ObservationClosure X observable)
    (P₁ P₂ : X → Prop)
    (h₁ : ∀ x, P₁ (C.cl x) ↔ observable (C.cl x))
    (h₂ : ∀ x, P₂ (C.cl x) ↔ observable (C.cl x)) :
    ∀ x, P₁ (C.cl x) ↔ P₂ (C.cl x) :=
  closure_rigidity_uniqueness C P₁ P₂ h₁ h₂

/-!
## Summary

This module provides:
1. `ObservationClosure` - abstract closure with observable preservation
2. `unique_extension_along_closure` - main rigidity theorem
3. `closure_rigidity_uniqueness` - corollary for predicate uniqueness
4. Instances:
   - T1 (upClosure on Trace)
   - DR1 abstract (kit-invariance)
   - Generic parameterized (arbitrary closure)
-/

end RevHalt.Theory
