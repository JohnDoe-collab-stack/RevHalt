import RevHalt.Theory.TheoryDynamics
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# RevHalt.Theory.TheoryDynamics_Transfinite

This module extends the core dynamics to transfinite ordinals.
It allows us to study the behavior of the system beyond the first limit ordinal ω.

## Key Definitions
- `transIter`: The ordinal-indexed iteration of the step function F.
- `limit_collapse_schema`: The theorem stating that frontier vanishes at limits under absorption.
-/

namespace RevHalt

open Set
open Ordinal

section TransfiniteDynamics

universe u

variable {PropT : Type u}

/--
  **Transfinite Union (Independent)**:
  The union of a global chain up to a limit.
-/
def transUnion (chain : Ordinal → Set PropT) (lim : Ordinal) : Set PropT :=
  { p | ∃ β, β < lim ∧ p ∈ chain β }

/--
  **Transfinite Union (Family)**:
  Helper for recursion, taking a dependent family.
-/
def transUnionFamily {α : Ordinal} (chain : ∀ β < α, Set PropT) : Set PropT :=
  { p | ∃ β, ∃ (h : β < α), p ∈ chain β h }

/--
  **Transfinite Iteration**:
  Recursively defines the state Γ_α for any ordinal α using `limitRecOn`.

  - Base: Γ_0 = A0
  - Successor: Γ_{α+1} = F(Γ_α)
  - Limit: Γ_λ = ⋃_{β<λ} Γ_β
-/
def transIter
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (α : Ordinal) : Set PropT :=
  Ordinal.limitRecOn α
    A0
    (fun _ prev => F prev)
    (fun _ _ chain => transUnionFamily chain)

-- ═══════════════════════════════════════════════════════════════════════════════
-- RECURSION LEMMAS
-- ═══════════════════════════════════════════════════════════════════════════════

@[simp]
theorem transIter_zero (F : Set PropT → Set PropT) (A0 : Set PropT) :
    transIter F A0 0 = A0 :=
  Ordinal.limitRecOn_zero _ _ _

@[simp]
theorem transIter_succ (F : Set PropT → Set PropT) (A0 : Set PropT) (α : Ordinal) :
    transIter F A0 (succ α) = F (transIter F A0 α) :=
  Ordinal.limitRecOn_succ _ _ _ _

theorem transIter_limit
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (λ : Ordinal)
    (hLim : Ordinal.IsLimit λ) :
    transIter F A0 λ = transUnion (transIter F A0) λ := by
  -- Unfold limit recursion
  rw [Ordinal.limitRecOn_limit _ _ _ _ hLim]
  -- Show family union equals global union
  dsimp [transUnion, transUnionFamily]
  ext p
  constructor
  · rintro ⟨β, hβ, hp⟩
    exact ⟨β, hβ, hp⟩
  · rintro ⟨β, hβ, hp⟩
    exact ⟨β, hβ, hp⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Transfinite Monotonicity**:
  If F is extensive (Γ ⊆ F(Γ)), then the transfinite iteration is monotone.
-/
theorem transIter_mono
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hExt : ∀ Γ, Γ ⊆ F Γ) :
    Monotone (transIter F A0) := by
  intro α β hle
  revert α
  induction β using Ordinal.limitRecOn with
  | zero => -- Base: β = 0
    intro α hle
    have : α = 0 := Ordinal.le_zero.mp hle
    subst this
    exact subset_rfl
  | succ γ ih => -- Succ: β = succ γ
    intro α hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · -- α < succ γ => α ≤ γ
      have h_le_γ : α ≤ γ := Ordinal.le_of_lt_succ hlt
      have h_sub_γ : transIter F A0 α ⊆ transIter F A0 γ := ih α h_le_γ
      rw [transIter_succ]
      exact subset_trans h_sub_γ (hExt (transIter F A0 γ))
    · -- α = succ γ
      exact subset_rfl
  | limit λ hLim ih => -- Limit: β = λ
    intro α hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · -- α < λ
      rw [transIter_limit _ _ _ hLim]
      exact fun p hp => ⟨α, hlt, hp⟩
    · -- α = λ
      exact subset_rfl

end TransfiniteDynamics

end RevHalt
