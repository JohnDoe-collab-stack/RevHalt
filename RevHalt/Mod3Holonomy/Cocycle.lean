/-
  RevHalt.Mod3Holonomy.Cocycle

  Strict formalization of Theorem B: The Flip is a cocycle (additive).

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §31
-/

import RevHalt.Mod3Holonomy.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace RevHalt.Mod3Holonomy

variable [Mod3Theory]

/-! ## Theorem B: Additivity of Flip on Paths

Flip(a, c) = Flip(a, b) + Flip(b, c)
-/

/-- The flip function is additive under path composition -/
theorem flip_additive (p q r : Path) :
    flip p r = flip p q + flip q r := by
  simp only [flip, monodromy]
  -- transport r - transport p = (transport q - transport p) + (transport r - transport q)
  ring

end RevHalt.Mod3Holonomy
