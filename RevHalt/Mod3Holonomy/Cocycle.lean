/-
  RevHalt.Mod3Holonomy.Cocycle

  Theorem B: Flip is a ℤ/2 cocycle

  Flip₃(β ∘ α) = Flip₃(β) ⊕ Flip₃(α)

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §31
-/

import RevHalt.Mod3Holonomy.Basic

namespace RevHalt.Mod3Holonomy

/-! ## Theorem B: Cocycle Property

The flip satisfies additivity under composition of 2-cells.
-/

/-- Monodromy is multiplicative -/
theorem monodromy_comp (T_p T_q T_r : Transport) :
    monodromy T_p T_r = monodromy T_q T_r * monodromy T_p T_q := by
  simp only [monodromy]
  group

/-- Helper: monodromy values are exactly id or tau -/
theorem monodromy_cases (T_p T_q : Transport) :
    monodromy T_p T_q = 1 ∨ monodromy T_p T_q = tau :=
  perm_dichotomy (monodromy T_p T_q)

/-- tau * tau = 1 -/
theorem tau_mul_tau : tau * tau = 1 := by
  ext x
  fin_cases x
  · decide
  · decide

/-- tau * 1 = tau -/
theorem tau_mul_one : tau * 1 = tau := by simp

/-- 1 * tau = tau -/
theorem one_mul_tau : 1 * tau = tau := by simp

/-- Flip is additive (XOR) under composition -/
theorem flip_additive (T_p T_q T_r : Transport) :
    flip T_p T_r = flip T_p T_q + flip T_q T_r := by
  -- Case analysis on the four possible combinations
  cases monodromy_cases T_p T_q with
  | inl h_pq_id =>
    cases monodromy_cases T_q T_r with
    | inl h_qr_id =>
      -- Both id: flip = 0 + 0 = 0, monodromy = id
      have h_pr : monodromy T_p T_r = 1 := by
        rw [monodromy_comp, h_qr_id, h_pq_id]
        simp
      simp only [flip, h_pq_id, h_qr_id, h_pr, ↓reduceIte]
      decide
    | inr h_qr_tau =>
      -- id * tau = tau: flip = 0 + 1 = 1
      have h_pr : monodromy T_p T_r = tau := by
        rw [monodromy_comp, h_qr_tau, h_pq_id]
        simp
      simp only [flip, h_pq_id, h_qr_tau, h_pr, ↓reduceIte, tau_ne_id]
      decide
  | inr h_pq_tau =>
    cases monodromy_cases T_q T_r with
    | inl h_qr_id =>
      -- tau * id = tau: flip = 1 + 0 = 1
      have h_pr : monodromy T_p T_r = tau := by
        rw [monodromy_comp, h_qr_id, h_pq_tau]
        simp
      simp only [flip, h_pq_tau, h_qr_id, h_pr, ↓reduceIte, tau_ne_id]
      decide
    | inr h_qr_tau =>
      -- tau * tau = id: flip = 1 + 1 = 0
      have h_pr : monodromy T_p T_r = 1 := by
        rw [monodromy_comp, h_qr_tau, h_pq_tau]
        exact tau_mul_tau
      simp only [flip, h_pq_tau, h_qr_tau, h_pr, ↓reduceIte, tau_ne_id]
      decide

/-- Flip defines a functor to B(ℤ/2) -/
theorem flip_cocycle : ∀ T_p T_q T_r : Transport,
    flip T_p T_r = flip T_p T_q + flip T_q T_r :=
  flip_additive

/-- Flip of identity transport is 0 -/
theorem flip_id (T : Transport) : flip T T = 0 := by
  simp only [flip, monodromy]
  simp

end RevHalt.Mod3Holonomy
