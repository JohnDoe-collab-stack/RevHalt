import Mathlib.ModelTheory.Semantics
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Theory.ArithmeticLanguage

This file sets up a minimal *first-order arithmetic* environment in mathlib's `FirstOrder` framework:

- a language with function symbols `0`, `succ`, `+`, `*`,
- an optional computation-facing relation symbol `evaln`,
- the standard structure on `ℕ`,
- and the associated external truth predicate `Truth` (satisfaction in `ℕ`).

It is intentionally lightweight: RevHalt's Gödel layer (`GodelIStandard`) treats provability as an
explicit interface, so this file only fixes the **syntax** and **standard-model semantics** needed
to state “true-but-unprovable” results in the classical sense.

Design note:
`evaln` is not part of “pure” first-order arithmetic (PA/Q). We include it as a *single extra
relation symbol* so that the Gödel/arithmetization layer can talk about bounded evaluation of
`Nat.Partrec.Code` programs as a definitional interface, without having to build a full
arithmetization of computation inside PA/Q.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open Nat.Partrec

/-- Function symbols of the arithmetic language: `0`, `succ`, `+`, `*`. -/
inductive Func : ℕ → Type 0
  | zero : Func 0
  | succ : Func 1
  | add  : Func 2
  | mul  : Func 2
deriving DecidableEq

/-- Relation symbols of the extended arithmetic language.

`evaln` is a 4-ary predicate interpreted in the standard model as:
`evaln k codeNat inputNat outputNat := (Code.evaln k (Code.ofNatCode codeNat) inputNat = some outputNat)`.
-/
inductive Rel : ℕ → Type 0
  | evaln : Rel 4
deriving DecidableEq

/-- First-order language of arithmetic (with an extra `evaln` relation symbol). -/
def Lang : FirstOrder.Language.{0, 0} where
  Functions := Func
  Relations := Rel

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
    cases r with
    | evaln =>
        intro x
        exact Nat.Partrec.Code.evaln (x 0) (Nat.Partrec.Code.ofNatCode (x 1)) (x 2) = some (x 3)

@[simp] theorem relMap_evaln (x : Fin 4 → ℕ) :
    FirstOrder.Language.Structure.RelMap (L := Lang) (M := ℕ) Rel.evaln x ↔
      Nat.Partrec.Code.evaln (x 0) (Nat.Partrec.Code.ofNatCode (x 1)) (x 2) = some (x 3) :=
  Iff.rfl

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
