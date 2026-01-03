import RevHalt.Theory.RobinsonQ
import RevHalt.Theory.ArithmeticProvability
import Mathlib.ModelTheory.Satisfiability

/-!
# RevHalt.Theory.RobinsonQProvability

This file provides a **baseline** provability predicate for Robinson arithmetic `Q`:

`Provable_Q_sem φ := QTheory ⊨ᵇ φ`

That is, “provable” is interpreted as **semantic consequence** (true in every nonempty model of `Q`).
This is intentionally lightweight and immediately yields a `ProvabilitySystem`:

- consistency follows from the existence of the standard model `ℕ ⊨ QTheory`,
- explosion is inherited from classical semantics.

Important note:
this is **not** the r.e. (syntactic) provability predicate needed for full “Gödel classical”.
It is the stable C1 baseline that makes the remaining obligations precise.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

/-- Semantic consequence (in all nonempty models of `QTheory`) as a baseline provability predicate. -/
def ProvableQSem (φ : Sentence) : Prop :=
  QTheory ⊨ᵇ φ

theorem provableQSem_consistent : ¬ ProvableQSem (⊥ : Sentence) := by
  intro hBot
  have hAll : ∀ M : QTheory.ModelType, M ⊨ (⊥ : Sentence) :=
    (FirstOrder.Language.Theory.models_sentence_iff (T := QTheory) (φ := (⊥ : Sentence))).1 hBot
  -- ℕ is a (nonempty) model of QTheory, so it cannot realize `⊥`.
  let M : QTheory.ModelType := (nat_models_QTheory).bundled
  have hM : M ⊨ (⊥ : Sentence) := hAll M
  simpa using hM

theorem provableQSem_absurd (p : Sentence) :
    ProvableQSem p → ProvableQSem p.not → ProvableQSem (⊥ : Sentence) := by
  intro hp hnp
  -- Reduce semantic consequence to satisfaction in each bundled model of QTheory.
  refine (FirstOrder.Language.Theory.models_sentence_iff (T := QTheory) (φ := (⊥ : Sentence))).2 ?_
  intro M
  have hpM :
      M ⊨ p :=
    (FirstOrder.Language.Theory.models_sentence_iff (T := QTheory) (φ := p)).1 hp M
  have hnpM :
      M ⊨ p.not :=
    (FirstOrder.Language.Theory.models_sentence_iff (T := QTheory) (φ := p.not)).1 hnp M
  have hNot : ¬ M ⊨ p := (FirstOrder.Language.Sentence.realize_not (M := M) (φ := p)).1 hnpM
  have hFalse : False := hNot hpM
  exact hFalse.elim

/-- `Q` as a `ProvabilitySystem`, using semantic consequence as the provability predicate. -/
def QProvabilitySystemSem : ProvabilitySystem where
  Provable := ProvableQSem
  consistent := provableQSem_consistent
  absurd := fun p hp hnp => provableQSem_absurd p hp hnp

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.ProvableQSem
#print axioms RevHalt.Arithmetic.provableQSem_consistent
#print axioms RevHalt.Arithmetic.provableQSem_absurd
#print axioms RevHalt.Arithmetic.QProvabilitySystemSem
