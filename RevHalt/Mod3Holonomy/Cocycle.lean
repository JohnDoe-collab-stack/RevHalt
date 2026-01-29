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
  simp [monodromy]
  group

/-- Flip is additive (XOR) under composition -/
theorem flip_additive (T_p T_q T_r : Transport) :
    flip T_p T_r = flip T_p T_q + flip T_q T_r := by
  -- This follows from monodromy_comp and the fact that
  -- Aut(Prim₃) ≅ ℤ/2 is abelian
  sorry  -- TODO: complete proof

/-- Flip defines a functor to B(ℤ/2) -/
theorem flip_cocycle : ∀ T_p T_q T_r : Transport,
    flip T_p T_r = flip T_p T_q + flip T_q T_r :=
  flip_additive

end RevHalt.Mod3Holonomy
