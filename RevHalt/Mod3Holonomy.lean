/-
  RevHalt.Mod3Holonomy

  Mod 3 Holonomy Theory - Complete Formalization

  This module formalizes the theory of mod 3 holonomy for dynamics:
  - Prim₃ : the primitive 2-element fiber at resolution 3
  - Transport : bijections on Prim₃ along paths
  - Monodromy and Flip : the ℤ/2 invariant
  - Cocycle property : Flip is additive (XOR)
  - Groupoid structure : 2-cells and the Flip functor
  - Self-repair : SR0, SR1, and the loop criterion

  Main theorems:
  - Theorem A : perm_dichotomy (every permutation is id or tau)
  - Theorem B : flip_additive (Flip is a ℤ/2 cocycle)
  - Theorem C : selfRepair_holds (SR1 always holds in abstract model)

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md
-/

import RevHalt.Mod3Holonomy.Basic
import RevHalt.Mod3Holonomy.Cocycle
import RevHalt.Mod3Holonomy.Groupoid
import RevHalt.Mod3Holonomy.SelfRepair
import RevHalt.Mod3Holonomy.Repaired
import RevHalt.Mod3Holonomy.Asymptotic
