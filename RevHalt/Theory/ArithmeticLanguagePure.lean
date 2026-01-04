import RevHalt.Theory.ArithmeticLanguage
import Mathlib.ModelTheory.LanguageMap

/-!
# RevHalt.Theory.ArithmeticLanguagePure

This file defines the **pure arithmetic sublanguage** of `RevHalt.Arithmetic.Lang`:

- same function symbols `0`, `succ`, `+`, `*`,
- **no additional relation symbols** (in particular, no `evaln`).

It also provides the canonical inclusion language map `Pure.toLang : Pure.Lang0 →ᴸ Arithmetic.Lang`
and the corresponding truth-transport lemma `Pure.truth_liftSentence`.

This is the staging point for the “full arithmetization” direction: a halting schema
`H : Code → Sentence` should ultimately live in `Pure.Lang0` and be transported to the ambient
language only via `Pure.toLang.onSentence`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-- Pure arithmetic language: same function symbols as `Arithmetic.Lang`, no relation symbols. -/
def Lang0 : FirstOrder.Language.{0, 0} where
  Functions := Func
  Relations := fun _ => PEmpty

/-- Inclusion of the pure arithmetic language into the ambient arithmetic language. -/
def toLang : Lang0 →ᴸ Lang where
  onFunction := by
    intro _n f
    exact f
  onRelation := by
    intro _n r
    exact PEmpty.elim r

-- Interpret `Lang0` on `ℕ` as the reduct of the ambient structure.
instance : Lang0.Structure ℕ :=
  (toLang.reduct (M := ℕ))

@[simp] theorem funMap_zero (x : Fin 0 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang0) (M := ℕ) Func.zero x = 0 := by
  rfl

@[simp] theorem funMap_succ (x : Fin 1 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang0) (M := ℕ) Func.succ x = Nat.succ (x 0) := by
  rfl

@[simp] theorem funMap_add (x : Fin 2 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang0) (M := ℕ) Func.add x = x 0 + x 1 := by
  rfl

@[simp] theorem funMap_mul (x : Fin 2 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang0) (M := ℕ) Func.mul x = x 0 * x 1 := by
  rfl

abbrev Sentence0 : Type :=
  Lang0.Sentence

/-- External (standard-model) truth for pure arithmetic sentences. -/
def Truth0 (φ : Sentence0) : Prop :=
  (ℕ : Type) ⊨ φ

@[simp] theorem truth0_not (φ : Sentence0) : Truth0 (φ.not) ↔ ¬ Truth0 φ := by
  rfl

/-- Lift a pure sentence into the ambient arithmetic language. -/
def liftSentence (φ : Sentence0) : Sentence :=
  toLang.onSentence φ

@[simp] theorem truth_liftSentence (φ : Sentence0) :
    Truth (liftSentence φ) ↔ Truth0 φ := by
  unfold Truth Truth0 liftSentence
  simp

end Pure

end Arithmetic

end RevHalt
