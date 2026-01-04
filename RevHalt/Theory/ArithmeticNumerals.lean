import RevHalt.Theory.ArithmeticEncoding
import Mathlib.Logic.Denumerable
import Mathlib.Computability.Primrec

/-!
# RevHalt.Theory.ArithmeticNumerals

This file provides a small but critical computability prerequisite for the Gödel track:
arithmetic sentences form an **infinite** (hence denumerable) type.

Why this matters:
- `Encodable Sentence` is available from `ArithmeticEncoding`.
- Many computability interfaces (r.e. / partial recursive) in mathlib are stated for
  `Primcodable` types; and `Primcodable` is available for any `Denumerable` type.
- To obtain `Denumerable Sentence` from mathlib, it suffices to provide `Infinite Sentence`.

We prove infinitude by an explicit injection `ℕ → Sentence`, using the usual numeral terms
`0, succ(0), succ(succ(0)), ...` and the injectivity of the syntactic constructors.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

abbrev ClosedTerm : Type :=
  Lang.Term (Empty ⊕ Fin 0)

def zeroTerm : ClosedTerm :=
  FirstOrder.Language.Term.func Func.zero (fun i => Fin.elim0 i)

def succTerm (t : ClosedTerm) : ClosedTerm :=
  FirstOrder.Language.Term.func Func.succ (fun _ => t)

def numeralTerm : ℕ → ClosedTerm
  | 0 => zeroTerm
  | n + 1 => succTerm (numeralTerm n)

theorem zeroTerm_ne_succTerm (t : ClosedTerm) : zeroTerm ≠ succTerm t := by
  intro h
  dsimp [zeroTerm, succTerm] at h
  have hInj := FirstOrder.Language.Term.func.inj (L := Lang) (α := Empty ⊕ Fin 0) h
  exact Nat.zero_ne_one hInj.1

theorem succTerm_injective : Function.Injective succTerm := by
  intro t u h
  dsimp [succTerm] at h
  have hInj := FirstOrder.Language.Term.func.inj (L := Lang) (α := Empty ⊕ Fin 0) h
  have hArgs : (fun _ : Fin 1 => t) = (fun _ : Fin 1 => u) :=
    eq_of_heq hInj.2.2
  have : t = u := by
    simpa using congrArg (fun g => g 0) hArgs
  exact this

theorem numeralTerm_injective : Function.Injective numeralTerm := by
  intro n m h
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => rfl
      | succ m =>
          have : zeroTerm = succTerm (numeralTerm m) := by
            simpa [numeralTerm] using h
          exact False.elim ((zeroTerm_ne_succTerm (t := numeralTerm m)) this)
  | succ n ih =>
      cases m with
      | zero =>
          have : zeroTerm = succTerm (numeralTerm n) := by
            simpa [numeralTerm] using h.symm
          exact False.elim ((zeroTerm_ne_succTerm (t := numeralTerm n)) this)
      | succ m =>
          have h' : numeralTerm n = numeralTerm m := by
            apply succTerm_injective
            simpa [numeralTerm] using h
          exact congrArg Nat.succ (ih h')

def numeralSentence (n : ℕ) : Sentence :=
  FirstOrder.Language.BoundedFormula.equal (L := Lang) (α := Empty) (n := 0) (numeralTerm n) zeroTerm

theorem numeralSentence_injective : Function.Injective numeralSentence := by
  intro n m h
  have hInj :=
    (FirstOrder.Language.BoundedFormula.equal.inj (L := Lang) (α := Empty) (n := 0) h)
  exact numeralTerm_injective hInj.1

instance : Infinite Sentence :=
  Infinite.of_injective numeralSentence numeralSentence_injective

instance : Denumerable Sentence :=
  Denumerable.ofEncodableOfInfinite Sentence

instance : Primcodable Sentence := by
  infer_instance

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.numeralTerm_injective
#print axioms RevHalt.Arithmetic.numeralSentence_injective
