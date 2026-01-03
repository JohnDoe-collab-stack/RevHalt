import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Theory.ArithmeticLanguage

This file sets up a minimal *first-order arithmetic* environment in mathlib's `FirstOrder` framework:

- a language with function symbols `0`, `succ`, `+`, `*`,
- the standard structure on `ℕ`,
- and the associated external truth predicate `Truth` (satisfaction in `ℕ`).

It is intentionally lightweight: RevHalt's Gödel layer (`GodelIStandard`) treats provability as an
explicit interface, so this file only fixes the **syntax** and **standard-model semantics** needed
to state “true-but-unprovable” results in the classical sense.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder

/-- Function symbols of the arithmetic language: `0`, `succ`, `+`, `*`. -/
inductive Func : ℕ → Type 0
  | zero : Func 0
  | succ : Func 1
  | add  : Func 2
  | mul  : Func 2
deriving DecidableEq

/-- First-order language of arithmetic (no relation symbols besides equality). -/
def Lang : FirstOrder.Language.{0, 0} where
  Functions := Func
  Relations := fun _ => PEmpty

instance : Lang.Structure ℕ where
  funMap := by
    intro n f
    cases f with
    | zero =>
        intro _x
        exact 0
    | succ =>
        intro x
        exact Nat.succ (x 0)
    | add =>
        intro x
        exact x 0 + x 1
    | mul =>
        intro x
        exact x 0 * x 1
  RelMap := by
    intro _n r
    cases r

@[simp] theorem funMap_zero (x : Fin 0 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang) (M := ℕ) Func.zero x = 0 := rfl

@[simp] theorem funMap_succ (x : Fin 1 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang) (M := ℕ) Func.succ x = Nat.succ (x 0) := rfl

@[simp] theorem funMap_add (x : Fin 2 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang) (M := ℕ) Func.add x = x 0 + x 1 := rfl

@[simp] theorem funMap_mul (x : Fin 2 → ℕ) :
    FirstOrder.Language.Structure.funMap (L := Lang) (M := ℕ) Func.mul x = x 0 * x 1 := rfl

abbrev Sentence : Type := Lang.Sentence

/-- External (standard-model) truth for arithmetic sentences. -/
def Truth (φ : Sentence) : Prop :=
  (ℕ : Type) ⊨ φ

@[simp] theorem truth_not (φ : Sentence) : Truth (φ.not) ↔ ¬ Truth φ := by
  rfl

end Arithmetic

end RevHalt
