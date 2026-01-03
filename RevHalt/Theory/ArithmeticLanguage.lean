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
inductive Func : ℕ → Type
  | zero : Func 0
  | succ : Func 1
  | add  : Func 2
  | mul  : Func 2
deriving DecidableEq

/-- First-order language of arithmetic (no relation symbols besides equality). -/
def Lang : FirstOrder.Language where
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

abbrev Sentence : Type := Lang.Sentence

/-- External (standard-model) truth for arithmetic sentences. -/
def Truth (φ : Sentence) : Prop :=
  (ℕ : Type) ⊨ φ

@[simp] theorem truth_not (φ : Sentence) : Truth (φ.not) ↔ ¬ Truth φ := by
  rfl

end Arithmetic

end RevHalt

