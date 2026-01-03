import RevHalt.Theory.ArithmeticLanguage
import RevHalt.Theory.Impossibility

/-!
# RevHalt.Theory.ArithmeticProvability

RevHalt’s Gödel layer (`ImpossibleSystem`, `GodelIStandard`) keeps provability abstract.
To talk about **standard arithmetic** (“true in ℕ”) we fix:

- `PropT := RevHalt.Arithmetic.Sentence` (first-order arithmetic sentences),
- negation/falsehood as the *syntactic* constructors `p.not` and `⊥`,
- and then treat the **provability predicate** as an explicit interface.

This file provides a small wrapper turning any `Provable : Sentence → Prop` satisfying minimal
consistency/absurdity into a `RevHalt.ImpossibleSystem`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder

/-- Minimal provability interface over arithmetic sentences (to be instantiated by PA/Q/etc.). -/
structure ProvabilitySystem where
  /-- Internal provability predicate for the chosen theory. -/
  Provable : Sentence → Prop
  /-- Consistency: the theory does not prove `⊥`. -/
  consistent : ¬ Provable (⊥ : Sentence)
  /-- Explosion at the provability level (enough for the Gödel barrier interfaces). -/
  absurd : ∀ p : Sentence, Provable p → Provable p.not → Provable (⊥ : Sentence)

/-- Turn an arithmetic provability interface into the abstract `ImpossibleSystem` used by T2/Gödel. -/
def ProvabilitySystem.toImpossibleSystem (T : ProvabilitySystem) : ImpossibleSystem Sentence where
  Provable := T.Provable
  FalseT := ⊥
  Not := fun p => p.not
  consistent := T.consistent
  absurd := fun p hp hnp => T.absurd p hp hnp

@[simp] theorem ProvabilitySystem.toImpossibleSystem_FalseT (T : ProvabilitySystem) :
    (T.toImpossibleSystem).FalseT = (⊥ : Sentence) := rfl

@[simp] theorem ProvabilitySystem.toImpossibleSystem_Not (T : ProvabilitySystem) (p : Sentence) :
    (T.toImpossibleSystem).Not p = p.not := rfl

end Arithmetic

end RevHalt

