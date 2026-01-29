/-
  RevHalt.Mod3Holonomy.Groupoid

  Strict formalization of the Scheduling Groupoid Π(h,k) for any Mod3Theory.

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §18
-/

import RevHalt.Mod3Holonomy.Basic
import RevHalt.Mod3Holonomy.Cocycle

namespace RevHalt.Mod3Holonomy

variable [Mod3Theory]

/-! ## The Scheduling Groupoid Structure -/

/-- A 2-cell (deformation) between two paths exists only if they have same Total -/
structure TwoCell where
  source : Path
  target : Path
  compatible : total source = total target
  deriving DecidableEq

/-- The flip of a 2-cell -/
def TwoCell.getFlip (α : TwoCell) : ZMod 2 :=
  flip α.source α.target

/-- Identity 2-cell -/
def TwoCell.id (p : Path) : TwoCell :=
  { source := p, target := p, compatible := rfl }

/-- Composition of 2-cells -/
def TwoCell.comp (α β : TwoCell) (h : α.target = β.source) : TwoCell :=
  { source := α.source
  , target := β.target
  , compatible := by rw [α.compatible, h, β.compatible] }

/-! ## Flip Functoriality -/

theorem TwoCell.getFlip_comp (α β : TwoCell) (h : α.target = β.source) :
    (TwoCell.comp α β h).getFlip = α.getFlip + β.getFlip := by
  simp only [TwoCell.getFlip, TwoCell.comp]
  rw [←h]
  apply flip_additive

/-! ## Cohomology Class and Non-Reduction -/

/-- A generic gauge on Paths -/
def Gauge := Path → ZMod 2

/-- A trivializing 1D gauge (depends only on Total) -/
def Gauge1D := Total1D → ZMod 2

/-- Is Cobalt (SR1): Flip is a coboundary on Paths (always true here) -/
def IsCoboundary : Prop :=
  ∃ g : Gauge, ∀ α : TwoCell, α.getFlip = g α.target - g α.source

/-- Is Reducible (Non-Reduction negation): Flip factors through Total -/
def IsReducible : Prop :=
  ∃ g1 : Gauge1D, ∀ α : TwoCell, α.getFlip = g1 (total α.target) - g1 (total α.source)

end RevHalt.Mod3Holonomy
