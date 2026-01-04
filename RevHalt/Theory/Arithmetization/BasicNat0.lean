import RevHalt.Theory.ArithmeticLanguagePure
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# RevHalt.Theory.Arithmetization.BasicNat0

Basic “pure arithmetic” utilities (no extra relation symbols).

This file provides small building blocks in the language `Arithmetic.Pure.Lang0` (only
`0,succ,+,*` and `=`) that are useful for the full arithmetization track:

- numerals as terms,
- definable order relations `≤` and `<` (encoded via existential witnesses),
- definable parity predicates (even/odd).

All correctness lemmas are stated in the standard model `ℕ`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-! ### Pure terms -/

def zeroTerm {α : Type} : Lang0.Term α :=
  FirstOrder.Language.Term.func Func.zero (fun i => Fin.elim0 i)

def succTerm {α : Type} (t : Lang0.Term α) : Lang0.Term α :=
  FirstOrder.Language.Term.func Func.succ (fun _ => t)

def addTerm {α : Type} (t u : Lang0.Term α) : Lang0.Term α :=
  FirstOrder.Language.Term.func Func.add ![t, u]

def mulTerm {α : Type} (t u : Lang0.Term α) : Lang0.Term α :=
  FirstOrder.Language.Term.func Func.mul ![t, u]

def numeralTerm {α : Type} : ℕ → Lang0.Term α
  | 0 => zeroTerm
  | n + 1 => succTerm (numeralTerm n)

@[simp] theorem numeralTerm_realize {α : Type} (n : ℕ) (v : α → ℕ) :
    (numeralTerm (α := α) n).realize v = n := by
  induction n with
  | zero => simp [numeralTerm, zeroTerm]
  | succ n ih => simp [numeralTerm, succTerm, ih]

/-! ### Order formulas (pure) -/

/-!
We encode order using existential witnesses, in the standard way:

- `x ≤ y` as `∃ k, x + k = y`
- `x < y` as `∃ k, succ x + k = y`
- `Even x` as `∃ k, x = 2*k`
- `Odd x`  as `∃ k, x = 2*k + 1`

These are *formula-level* definitions in the pure language `Lang0` (no extra relation symbols).
-/

private def fvar {α : Type} {n : ℕ} (a : α) : Lang0.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.var (Sum.inl a)

private def bvar {α : Type} {n : ℕ} (i : Fin n) : Lang0.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.var (Sum.inr i)

/-- Extend a finite valuation by one new entry (with `α := fun _ => ℕ` fixed for elaboration). -/
def snocNat {n : ℕ} (xs : Fin n → ℕ) (a : ℕ) : Fin (n + 1) → ℕ :=
  Fin.snoc (α := fun _ : Fin (n + 1) => ℕ) xs a

@[simp] theorem snocNat_castSucc {n : ℕ} (xs : Fin n → ℕ) (a : ℕ) (i : Fin n) :
    snocNat xs a i.castSucc = xs i := by
  simp [snocNat, Fin.snoc_castSucc]

@[simp] theorem snocNat_last {n : ℕ} (xs : Fin n → ℕ) (a : ℕ) :
    snocNat xs a (Fin.last n) = a := by
  simp [snocNat, Fin.snoc_last]

private def liftBoundVar {α : Type} {n : ℕ} : (α ⊕ Fin n) → (α ⊕ Fin (n + 1))
  | Sum.inl a => Sum.inl a
  | Sum.inr i => Sum.inr i.castSucc

private def liftBoundTerm {α : Type} {n : ℕ} (t : Lang0.Term (α ⊕ Fin n)) :
    Lang0.Term (α ⊕ Fin (n + 1)) :=
  t.relabel liftBoundVar

/-- Bounded `≤` on terms: `t ≤ u` iff `∃ k, t + k = u`. -/
def bdLe {α : Type} {n : ℕ} (t u : Lang0.Term (α ⊕ Fin n)) : Lang0.BoundedFormula α n :=
  ∃'
    (FirstOrder.Language.Term.bdEqual
      (addTerm (liftBoundTerm t) (bvar (α := α) (n := n + 1) (Fin.last n)))
      (liftBoundTerm u))

/-- Bounded `<` on terms: `t < u` iff `∃ k, succ t + k = u`. -/
def bdLt {α : Type} {n : ℕ} (t u : Lang0.Term (α ⊕ Fin n)) : Lang0.BoundedFormula α n :=
  ∃'
    (FirstOrder.Language.Term.bdEqual
      (addTerm (succTerm (liftBoundTerm t)) (bvar (α := α) (n := n + 1) (Fin.last n)))
      (liftBoundTerm u))

@[simp] theorem bdLe_realize {α : Type} {n : ℕ} (t u : Lang0.Term (α ⊕ Fin n))
    (v : α → ℕ) (xs : Fin n → ℕ) :
    (bdLe (α := α) (n := n) t u).Realize v xs ↔
      t.realize (Sum.elim v xs) ≤ u.realize (Sum.elim v xs) := by
  have hLift (k : ℕ) :
      (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar) = Sum.elim v xs := by
    funext z
    cases z with
    | inl a => rfl
    | inr i =>
        simp [liftBoundVar, Fin.snoc_castSucc]
  constructor
  · intro h
    rcases
        (by
          simpa [bdLe, addTerm, bvar, liftBoundTerm, liftBoundVar] using h) with
      ⟨k, hk⟩
    have hk' : t.realize (Sum.elim v xs) + k = u.realize (Sum.elim v xs) := by
      simpa [FirstOrder.Language.Term.realize_relabel, liftBoundTerm, hLift k] using hk
    exact le_iff_exists_add.2 ⟨k, hk'.symm⟩
  · intro htu
    rcases (le_iff_exists_add).1 htu with ⟨k, hk⟩
    have hk' : t.realize (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar) + k =
        u.realize (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar) := by
      simpa [hLift k] using hk.symm
    simpa [bdLe, addTerm, bvar, liftBoundTerm, liftBoundVar, FirstOrder.Language.Term.realize_relabel] using
      ⟨k, hk'⟩

@[simp] theorem bdLt_realize {α : Type} {n : ℕ} (t u : Lang0.Term (α ⊕ Fin n))
    (v : α → ℕ) (xs : Fin n → ℕ) :
    (bdLt (α := α) (n := n) t u).Realize v xs ↔
      t.realize (Sum.elim v xs) < u.realize (Sum.elim v xs) := by
  have hLift (k : ℕ) :
      (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar) = Sum.elim v xs := by
    funext z
    cases z with
    | inl a => rfl
    | inr i =>
        simp [liftBoundVar, Fin.snoc_castSucc]
  constructor
  · intro h
    rcases
        (by
          simpa [bdLt, addTerm, bvar, liftBoundTerm, liftBoundVar, succTerm] using h) with
      ⟨k, hk⟩
    have hk' : Nat.succ (t.realize (Sum.elim v xs)) + k = u.realize (Sum.elim v xs) := by
      simpa [FirstOrder.Language.Term.realize_relabel, liftBoundTerm, hLift k, succTerm, addTerm] using hk
    have hx1le : Nat.succ (t.realize (Sum.elim v xs)) ≤ u.realize (Sum.elim v xs) :=
      le_iff_exists_add.2 ⟨k, hk'.symm⟩
    exact (Nat.lt_iff_add_one_le).2 hx1le
  · intro htu
    have hx1le : Nat.succ (t.realize (Sum.elim v xs)) ≤ u.realize (Sum.elim v xs) :=
      (Nat.lt_iff_add_one_le).1 htu
    rcases (le_iff_exists_add).1 hx1le with ⟨k, hk⟩
    have hk' : Nat.succ (t.realize (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar)) + k =
        u.realize (Sum.elim v (Fin.snoc xs k) ∘ liftBoundVar) := by
      simpa [hLift k] using hk.symm
    simpa [bdLt, addTerm, bvar, liftBoundTerm, liftBoundVar, succTerm,
      FirstOrder.Language.Term.realize_relabel] using ⟨k, hk'⟩

/-- The formula `x ≤ y` for two free variables. -/
def leFormula : Lang0.Formula (Fin 2) :=
  bdLe (fvar (α := Fin 2) (n := 0) 0) (fvar (α := Fin 2) (n := 0) 1)

/-- The formula `x < y` for two free variables. -/
def ltFormula : Lang0.Formula (Fin 2) :=
  bdLt (fvar (α := Fin 2) (n := 0) 0) (fvar (α := Fin 2) (n := 0) 1)

@[simp] theorem leFormula_realize (x y : ℕ) :
    leFormula.Realize ![x, y] ↔ x ≤ y := by
  constructor
  · intro h
    rcases
        (by
          simpa [FirstOrder.Language.Formula.Realize, leFormula, bdLe, fvar, bvar, liftBoundTerm,
            liftBoundVar, addTerm] using h) with ⟨k, hk⟩
    exact le_iff_exists_add.2 ⟨k, hk.symm⟩
  · intro hxy
    rcases (le_iff_exists_add).1 hxy with ⟨k, hk⟩
    -- Rebuild the realization from the witness `k`.
    simpa [FirstOrder.Language.Formula.Realize, leFormula, bdLe, fvar, bvar, liftBoundTerm, liftBoundVar,
      addTerm] using ⟨k, hk.symm⟩

@[simp] theorem ltFormula_realize (x y : ℕ) :
    ltFormula.Realize ![x, y] ↔ x < y := by
  constructor
  · intro h
    -- `simp` unfolds the formula to the witness equation `succ x + k = y`.
    rcases
        (by
          simpa [FirstOrder.Language.Formula.Realize, ltFormula, bdLt, fvar, bvar, liftBoundTerm,
            liftBoundVar, addTerm, succTerm] using h) with ⟨k, hk⟩
    have hx1le : Nat.succ x ≤ y := le_iff_exists_add.2 ⟨k, hk.symm⟩
    exact (Nat.lt_iff_add_one_le).2 hx1le
  · intro hxy
    have hx1le : Nat.succ x ≤ y := (Nat.lt_iff_add_one_le).1 hxy
    rcases (le_iff_exists_add).1 hx1le with ⟨k, hk⟩
    -- Rebuild the realization.
    simpa [FirstOrder.Language.Formula.Realize, ltFormula, bdLt, fvar, bvar, liftBoundTerm, liftBoundVar,
      addTerm, succTerm] using ⟨k, hk.symm⟩

/-! ### Parity (pure) -/

/-- The formula `Even x` (one free variable). -/
def evenFormula : Lang0.Formula (Fin 1) :=
  ∃'
    (FirstOrder.Language.Term.bdEqual
      (fvar (α := Fin 1) (n := 1) 0)
      (addTerm (bvar (α := Fin 1) (n := 1) (Fin.last 0)) (bvar (α := Fin 1) (n := 1) (Fin.last 0))))

/-- The formula `Odd x` (one free variable). -/
def oddFormula : Lang0.Formula (Fin 1) :=
  ∃'
    (FirstOrder.Language.Term.bdEqual
      (fvar (α := Fin 1) (n := 1) 0)
      (addTerm
        (addTerm
          (bvar (α := Fin 1) (n := 1) (Fin.last 0))
          (bvar (α := Fin 1) (n := 1) (Fin.last 0)))
        (numeralTerm (α := Fin 1 ⊕ Fin 1) 1)))

@[simp] theorem evenFormula_realize (x : ℕ) :
    evenFormula.Realize ![x] ↔ Even x := by
  constructor
  · intro h
    rcases
        (by
          simpa [FirstOrder.Language.Formula.Realize, evenFormula, fvar, bvar, addTerm] using h) with
      ⟨k, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    simpa [FirstOrder.Language.Formula.Realize, evenFormula, fvar, bvar, addTerm] using ⟨k, hk⟩

@[simp] theorem oddFormula_realize (x : ℕ) :
    oddFormula.Realize ![x] ↔ Odd x := by
  constructor
  · intro h
    rcases
        (by
          simpa [FirstOrder.Language.Formula.Realize, oddFormula, fvar, bvar, addTerm, numeralTerm,
            succTerm, zeroTerm] using h) with
      ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [two_mul, add_assoc] using hk
  · rintro ⟨k, hk⟩
    have hk' : x = k + k + 1 := by
      simpa [two_mul, add_assoc] using hk
    simpa [FirstOrder.Language.Formula.Realize, oddFormula, fvar, bvar, addTerm, numeralTerm, succTerm, zeroTerm,
      two_mul, add_assoc] using ⟨k, hk'⟩

end Pure

end Arithmetic

end RevHalt
