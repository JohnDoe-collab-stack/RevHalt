import RevHalt.Theory.ArithmeticLanguage
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# RevHalt.Theory.RobinsonQ

This file defines a concrete arithmetic **theory** inside the first-order arithmetic language
from `RevHalt.Theory.ArithmeticLanguage`:

- Robinson arithmetic `Q` (a small finite axiom set in the language `0, succ, +, *`).

Why this matters for the Gödel track:

- `GodelIArithmetic` already fixes `PropT := Sentence` and `Truth :=` satisfaction in `ℕ`.
- To reach “Gödel classical (PA/Q)”, one still has to instantiate a *provability predicate* for a
  concrete theory (PA or Q) and the arithmetization-of-computation bridge `H`.

This file supplies the missing **theory object** (the axiom set) so that the remaining work can be
stated as: “build a proof system for this theory (or assume one), then build `H`”.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

/-! ## Term helpers (bounded-variable context) -/

private def zeroTerm {α : Type} {n : ℕ} : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.zero (fun i => Fin.elim0 i)

private def succTerm {α : Type} {n : ℕ} (t : Lang.Term (α ⊕ Fin n)) : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.succ (fun _ => t)

private def addTerm {α : Type} {n : ℕ} (t u : Lang.Term (α ⊕ Fin n)) : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.add ![t, u]

private def mulTerm {α : Type} {n : ℕ} (t u : Lang.Term (α ⊕ Fin n)) : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.mul ![t, u]

/-! ## Robinson Q axioms (one common presentation) -/

-- Q1: ∀x, succ x ≠ 0
def Q1 : Sentence :=
  ∀' ∼(succTerm (&0) =' zeroTerm)

-- Q2: ∀x∀y, succ x = succ y → x = y
def Q2 : Sentence :=
  ∀' ∀' ((succTerm (&1) =' succTerm (&0)) ⟹ (&1 =' &0))

-- Q3: ∀x, x ≠ 0 → ∃y, succ y = x
def Q3 : Sentence :=
  -- NOTE: in mathlib's bounded-variable convention, the new witness introduced by `∃'`
  -- is appended at the end (so `&0` still refers to the outer `x`, and `&1` to the witness `y`).
  ∀' ((∼(&0 =' zeroTerm)) ⟹ ∃' (succTerm (&1) =' &0))

-- Q4: ∀x, x + 0 = x
def Q4 : Sentence :=
  ∀' (addTerm (&0) zeroTerm =' &0)

-- Q5: ∀x∀y, x + succ y = succ (x + y)
def Q5 : Sentence :=
  ∀' ∀' (addTerm (&1) (succTerm (&0)) =' succTerm (addTerm (&1) (&0)))

-- Q6: ∀x, x * 0 = 0
def Q6 : Sentence :=
  ∀' (mulTerm (&0) zeroTerm =' zeroTerm)

-- Q7: ∀x∀y, x * succ y = (x * y) + x
def Q7 : Sentence :=
  ∀' ∀' (mulTerm (&1) (succTerm (&0)) =' addTerm (mulTerm (&1) (&0)) (&1))

/-- Robinson arithmetic `Q` as a theory (finite axiom set). -/
def QTheory : Lang.Theory :=
  {Q1, Q2, Q3, Q4, Q5, Q6, Q7}

/-! ## Soundness in the standard model ℕ (semantic checks) -/

theorem truth_Q1 : Truth Q1 := by
  -- ∀x, succ x ≠ 0
  unfold Truth
  simp [Q1, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    succTerm, zeroTerm]

theorem truth_Q2 : Truth Q2 := by
  -- ∀x∀y, succ x = succ y → x = y
  unfold Truth
  simp [Q2, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize, succTerm]

theorem truth_Q3 : Truth Q3 := by
  -- ∀x, x ≠ 0 → ∃y, succ y = x
  unfold Truth
  -- We expand `∃'` (`BoundedFormula.ex = ¬∀¬`) to keep the proof constructive
  -- (avoids the classical simp lemma `BoundedFormula.realize_ex`).
  simp only [Q3, FirstOrder.Language.BoundedFormula.ex]
  -- Unfold satisfaction and the outer `∀` / `→` structure, but do not rewrite `¬∀` into `∃`.
  unfold FirstOrder.Language.Sentence.Realize
  unfold FirstOrder.Language.Formula.Realize
  simp only [FirstOrder.Language.BoundedFormula.realize_all,
    FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_not]
  intro x hx0 hAll
  cases x with
  | zero => exact (hx0 rfl).elim
  | succ y =>
      -- Contradict the “∀y, ¬(succ y = x)” side by exhibiting the predecessor witness.
      exact (hAll y) (by
        simp [succTerm, Fin.snoc])

theorem truth_Q4 : Truth Q4 := by
  -- ∀x, x + 0 = x
  unfold Truth
  simp [Q4, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    addTerm, zeroTerm]

theorem truth_Q5 : Truth Q5 := by
  -- ∀x∀y, x + succ y = succ (x + y)
  unfold Truth
  simp [Q5, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    addTerm, succTerm, Fin.snoc, Nat.add_assoc]

theorem truth_Q6 : Truth Q6 := by
  -- ∀x, x * 0 = 0
  unfold Truth
  simp [Q6, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    mulTerm, zeroTerm]

theorem truth_Q7 : Truth Q7 := by
  -- ∀x∀y, x * succ y = (x * y) + x
  unfold Truth
  simp [Q7, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    mulTerm, addTerm, succTerm, Fin.snoc, Nat.mul_add]

/-- The standard model `ℕ` is a model of the Robinson theory `Q`. -/
theorem nat_models_QTheory : (ℕ : Type) ⊨ QTheory := by
  -- Expand membership in the finite axiom set and dispatch to the per-axiom proofs.
  refine ⟨?_⟩
  intro φ hφ
  simp [QTheory] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact truth_Q1
  · exact truth_Q2
  · exact truth_Q3
  · exact truth_Q4
  · exact truth_Q5
  · exact truth_Q6
  · exact truth_Q7

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.truth_Q1
#print axioms RevHalt.Arithmetic.truth_Q2
#print axioms RevHalt.Arithmetic.truth_Q3
#print axioms RevHalt.Arithmetic.truth_Q4
#print axioms RevHalt.Arithmetic.truth_Q5
#print axioms RevHalt.Arithmetic.truth_Q6
#print axioms RevHalt.Arithmetic.truth_Q7
#print axioms RevHalt.Arithmetic.nat_models_QTheory
