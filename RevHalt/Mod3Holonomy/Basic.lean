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
  have : plus = minus := by
    have := Equiv.congr_fun h plus
    simp [tau, Equiv.swap_apply_left] at this
    exact this
  simp [plus, minus] at this

/-- Every permutation of Prim₃ is either id or tau -/
theorem perm_dichotomy (σ : Transport) : σ = 1 ∨ σ = tau := by
  have h := Fintype.card_eq_two_iff.mp aut_prim₃_is_Z2
  -- The permutation group has exactly 2 elements
  fin_cases σ using Equiv.Perm.decidableEq
  all_goals { simp [tau, Equiv.swap] }
  sorry  -- TODO: complete case analysis

/-! ## Flip: the ℤ/2 invariant -/

/-- Flip₃(α) ∈ ℤ/2 : 0 if monodromy = id, 1 if monodromy = tau -/
def flip (T_p T_q : Transport) : ZMod 2 :=
  if monodromy T_p T_q = 1 then 0 else 1

/-- Flip is 0 iff monodromy is identity -/
theorem flip_zero_iff_id (T_p T_q : Transport) :
    flip T_p T_q = 0 ↔ monodromy T_p T_q = 1 := by
  simp [flip]

/-- Flip is 1 iff monodromy is tau -/
theorem flip_one_iff_tau (T_p T_q : Transport) :
    flip T_p T_q = 1 ↔ monodromy T_p T_q = tau := by
  simp [flip]
  intro h
  cases perm_dichotomy (monodromy T_p T_q) with
  | inl hid => exact absurd hid h
  | inr htau => exact htau

end RevHalt.Mod3Holonomy
