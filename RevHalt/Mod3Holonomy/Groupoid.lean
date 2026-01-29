/-
  RevHalt.Mod3Holonomy.Groupoid

  The scheduling groupoid Π(h,k) and the Flip functor to B(ℤ/2)

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §18-22
-/

import RevHalt.Mod3Holonomy.Basic
import RevHalt.Mod3Holonomy.Cocycle
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Groupoid

namespace RevHalt.Mod3Holonomy

open CategoryTheory

/-! ## The Scheduling Groupoid

The scheduling groupoid Π(h,k) has:
- Objects: paths (totals) p : h → k
- Morphisms: 2-cells α : p ⇒ q (deformations)
- All morphisms are invertible (localization)

We model this abstractly as a groupoid with transports as objects.
-/

/-- A 2-cell between two transports -/
structure TwoCell where
  source : Transport
  target : Transport
  deriving DecidableEq

/-- The flip of a 2-cell -/
def TwoCell.getFlip (α : TwoCell) : ZMod 2 :=
  flip α.source α.target

/-- Identity 2-cell -/
def TwoCell.id (T : Transport) : TwoCell := ⟨T, T⟩

/-- Composition of 2-cells -/
def TwoCell.comp (α β : TwoCell) (_ : α.target = β.source) : TwoCell :=
  ⟨α.source, β.target⟩

/-- Flip is additive under composition -/
theorem TwoCell.getFlip_comp (α β : TwoCell) (h : α.target = β.source) :
    (TwoCell.comp α β h).getFlip = α.getFlip + β.getFlip := by
  simp only [TwoCell.getFlip, TwoCell.comp]
  -- Need to show: flip α.source β.target = flip α.source α.target + flip α.target β.target
  have := flip_additive α.source α.target β.target
  rw [← h]
  exact this

/-! ## B(ℤ/2) : The classifying groupoid

B(ℤ/2) has one object and Aut(*) = ℤ/2.
The Flip functor sends each 2-cell to its flip value.
-/

/-- The Flip map is a groupoid homomorphism to ℤ/2 -/
theorem flip_functor_additive : ∀ α β : TwoCell, ∀ h : α.target = β.source,
    (TwoCell.comp α β h).getFlip = α.getFlip + β.getFlip :=
  TwoCell.getFlip_comp

/-- Flip of identity is 0 -/
theorem flip_functor_id (T : Transport) : (TwoCell.id T).getFlip = 0 := by
  simp only [TwoCell.getFlip, TwoCell.id, flip_id]

/-! ## Cohomology Class

The flip defines a class [Flip₃] ∈ H¹(Π(h,k); ℤ/2).
This class is zero iff there exists a gauge g such that
Flip(α) = g(target) - g(source) for all α.
-/

/-- A gauge is a function from transports to ℤ/2 -/
def Gauge := Transport → ZMod 2

/-- Flip is a coboundary iff there exists a gauge -/
def IsCoboundary : Prop :=
  ∃ g : Gauge, ∀ α : TwoCell, α.getFlip = g α.target - g α.source

/-- If flip is a coboundary, loops have zero flip -/
theorem coboundary_implies_loops_zero (_ : IsCoboundary) :
    ∀ T : Transport, (TwoCell.id T).getFlip = 0 :=
  fun T => flip_functor_id T

/-- Loops have zero flip (automatic from definition) -/
theorem loop_flip_zero (T : Transport) : (TwoCell.id T).getFlip = 0 :=
  flip_functor_id T

end RevHalt.Mod3Holonomy
