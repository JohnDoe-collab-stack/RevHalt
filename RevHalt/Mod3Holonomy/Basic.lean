/-
  RevHalt.Mod3Holonomy.Basic

  Formalization of Mod 3 Holonomy Theory

  This module defines:
  - Prim₃ : the primitive 2-element fiber at resolution 3
  - Transport T_p : bijection on Prim₃ along paths
  - Mono₃ : monodromy = T_q⁻¹ ∘ T_p
  - Flip₃ : the ℤ/2 invariant (identity vs transposition)

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin

namespace RevHalt.Mod3Holonomy

/-! ## Primitive Fiber at Resolution 3

The primitive fiber Prim₃(h) has exactly 2 elements.
We model this as `Fin 2` or equivalently `Bool`.
-/

/-- The primitive fiber type: exactly 2 elements -/
abbrev Prim₃ := Fin 2

/-- The two elements of Prim₃ -/
def plus : Prim₃ := 0
def minus : Prim₃ := 1

/-- plus and minus are distinct -/
theorem plus_ne_minus : plus ≠ minus := by decide

/-- Every element of Fin 2 is 0 or 1 -/
theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-! ## Transport along paths

Under hypothesis (INV3), transport T_p restricts to a bijection on Prim₃.
-/

/-- Transport on Prim₃ is a permutation (bijection) -/
abbrev Transport := Equiv.Perm Prim₃

/-- The group of automorphisms of Prim₃ is ℤ/2 -/
theorem aut_prim₃_is_Z2 : Fintype.card (Equiv.Perm Prim₃) = 2 := by
  simp [Fintype.card_perm]

/-! ## Monodromy and Flip

For a 2-cell α : p ⇒ q, the monodromy is Mono₃(α) = T_q⁻¹ ∘ T_p
-/

/-- Monodromy from two transports -/
def monodromy (T_p T_q : Transport) : Transport := T_q⁻¹ * T_p

/-- The unique non-trivial involution (transposition) on Prim₃ -/
def tau : Transport := Equiv.swap plus minus

/-- tau is the unique non-identity element -/
theorem tau_ne_id : tau ≠ 1 := by
  intro h
  have heq : tau plus = plus := by rw [h]; rfl
  simp only [tau, Equiv.swap_apply_left] at heq
  exact plus_ne_minus heq.symm

/-- Every permutation of Prim₃ is either id or tau (Theorem A core) -/
theorem perm_dichotomy (σ : Transport) : σ = 1 ∨ σ = tau := by
  -- Fin 2 has exactly 2 permutations: id and swap
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := fin2_cases (σ 0)
  have h1 : σ 1 = 0 ∨ σ 1 = 1 := fin2_cases (σ 1)
  cases h0 with
  | inl h0eq0 =>
    -- σ 0 = 0, so σ 1 = 1 (bijection)
    have h1eq1 : σ 1 = 1 := by
      cases h1 with
      | inl h1eq0 =>
        exfalso
        have : (0 : Fin 2) = 1 := σ.injective (h0eq0.trans h1eq0.symm)
        exact Fin.zero_ne_one this
      | inr h1eq1 => exact h1eq1
    left
    ext x
    fin_cases x <;> simp [h0eq0, h1eq1]
  | inr h0eq1 =>
    -- σ 0 = 1, so σ 1 = 0 (bijection) = tau
    have h1eq0 : σ 1 = 0 := by
      cases h1 with
      | inl h1eq0 => exact h1eq0
      | inr h1eq1 =>
        exfalso
        have : (0 : Fin 2) = 1 := σ.injective (h0eq1.trans h1eq1.symm)
        exact Fin.zero_ne_one this
    right
    ext x
    fin_cases x
    · -- Goal: (σ 0).val = (tau 0).val
      have htau0 : (tau 0 : Fin 2) = 1 := by decide
      exact congrArg Fin.val (h0eq1.trans htau0.symm)
    · -- Goal: (σ 1).val = (tau 1).val
      have htau1 : (tau 1 : Fin 2) = 0 := by decide
      exact congrArg Fin.val (h1eq0.trans htau1.symm)

/-! ## Flip: the ℤ/2 invariant -/

/-- Flip₃(α) ∈ ℤ/2 : 0 if monodromy = id, 1 if monodromy = tau -/
def flip (T_p T_q : Transport) : ZMod 2 :=
  if monodromy T_p T_q = 1 then 0 else 1

/-- Flip is 0 iff monodromy is identity -/
theorem flip_zero_iff_id (T_p T_q : Transport) :
    flip T_p T_q = 0 ↔ monodromy T_p T_q = 1 := by
  simp only [flip]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Flip is 1 iff monodromy is tau -/
theorem flip_one_iff_tau (T_p T_q : Transport) :
    flip T_p T_q = 1 ↔ monodromy T_p T_q = tau := by
  simp only [flip]
  constructor
  · intro hflip
    split_ifs at hflip with h
    · simp at hflip
    · cases perm_dichotomy (monodromy T_p T_q) with
      | inl hid => exact absurd hid h
      | inr htau => exact htau
  · intro htau
    split_ifs with h
    · exfalso
      rw [htau] at h
      exact tau_ne_id h
    · rfl

end RevHalt.Mod3Holonomy
