/-
  RevHalt.Mod3Holonomy.Basic

  Strict formalization of Mod 3 Holonomy using Typeclasses.
  This allows strict separation of syntax (Path) and semantics (Transport)
  without using axioms or opaque types that break code generation.

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md
-/

import Mathlib.Data.ZMod.Basic

namespace RevHalt.Mod3Holonomy

/-! ## The Mod3Theory Typeclass

We capture the structural requirements in a typeclass.
This allows us to reason about ANY model satisfying the strict definitions.
-/

class Mod3Theory where
  /-- The type of Paths (Schedulings) -/
  Path : Type
  /-- Paths must have decidable equality -/
  [pathDec : DecidableEq Path]

  /-- The type of 1D Totals -/
  Total1D : Type
  /-- Totals must have decidable equality -/
  [totalDec : DecidableEq Total1D]

  /-- (O3) The projection to 1D Total -/
  total : Path → Total1D

  /-- (INV3) Transport along a path (modeled as ZMod 2 value) -/
  transport : Path → ZMod 2

attribute [instance] Mod3Theory.pathDec
attribute [instance] Mod3Theory.totalDec

export Mod3Theory (Path Total1D total transport)

/-! ## Definitions (Generic over any Mod3Theory) -/

variable [Mod3Theory]

/-- (Mono3) Monodromy of a deformation α : p ⇒ q -/
def monodromy (p q : Path) : ZMod 2 :=
  transport q - transport p

/-- (Flip3) The flip value -/
def flip (p q : Path) : ZMod 2 :=
  monodromy p q

end RevHalt.Mod3Holonomy
