import RevHalt.Theory.ConvergenceSigma1
import RevHalt.Theory.ArithmeticLanguage
import RevHalt.Theory.RECodePred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# RevHalt.Theory.Arithmetization.HaltsSigma1

This file records the **Σ₁ witness shape** of halting (at the `Nat.Partrec.Code` level) and
packages the exact interface expected by the arithmetic Gödel layer.

The main point is to separate:

- the *computability-level* Σ₁ statement `∃ k x, evaln k e 0 = some x`, and
- the *arithmetic-level* sentence family `H : Code → Sentence` that should represent it in `ℕ`.

This is the staging bridge needed for a full “Gödel classical” instantiation:
once you provide a definition of `H` with `Truth (H e) ↔ HaltsSigma1 e`, `truth_H` for
`Rev0_K K (Machine e)` follows automatically.
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec
open FirstOrder
open scoped FirstOrder

/-- The Σ₁ halting predicate on codes: halting is witnessed by a bounded evaluation. -/
def HaltsSigma1 (e : Code) : Prop :=
  ∃ k x, Nat.Partrec.Code.evaln k e 0 = some x

/-- `HaltsSigma1` is exactly `Rev0_K K (Machine e)` for a monotone kit. -/
theorem haltsSigma1_iff_rev0_K (K : RHKit) (hK : DetectsMonotone K) (e : Code) :
    HaltsSigma1 e ↔ Rev0_K K (Machine e) := by
  simpa [HaltsSigma1] using (RevHalt.rev0_K_machine_iff_exists_evaln (K := K) (hK := hK) e).symm

/-! ### r.e. packaging (semi-decidability) -/

/--
`HaltsSigma1` is r.e. as an `RECodePred`, witnessed by the partial evaluator `Code.eval`.

This is the standard “Σ₁ witness → semi-decidable” packaging: halting is witnessed by a finite stage.
-/
def reHaltsSigma1 : RECodePred HaltsSigma1 where
  f := Nat.Partrec.Code.eval
  f_partrec := Nat.Partrec.Code.eval_part
  spec := by
    intro e
    -- `Converges e` is definitional `∃ x, x ∈ e.eval 0`.
    -- `converges_iff_exists_evaln` identifies it with the Σ₁ witness form.
    simpa [RevHalt.Converges, HaltsSigma1] using (RevHalt.converges_iff_exists_evaln e).symm

/--
For a monotone kit, `Rev0_K K (Machine e)` is r.e. (semi-decidable) on codes.

We reuse the same semi-decider `Code.eval`, and transport along `haltsSigma1_iff_rev0_K`.
-/
def reRev0KMachine (K : RHKit) (hK : DetectsMonotone K) :
    RECodePred fun e : Code => Rev0_K K (Machine e) where
  f := reHaltsSigma1.f
  f_partrec := reHaltsSigma1.f_partrec
  spec := by
    intro e
    exact (haltsSigma1_iff_rev0_K (K := K) (hK := hK) e).symm.trans (reHaltsSigma1.spec e)

/--
Arithmetic-level arithmetization requirement for halting:
`H` represents the Σ₁ predicate `HaltsSigma1` in the standard model.
-/
def ArithmetizesEvaln (H : Code → Sentence) : Prop :=
  ∀ e, Truth (H e) ↔ HaltsSigma1 e

/-! ### A concrete `H` in the extended arithmetic language

Because `ArithmeticLanguage` includes `Rel.evaln` as a primitive relation symbol, we can define
an explicit Σ₁ sentence family `H_evaln` and show it satisfies `ArithmetizesEvaln`.

This is an **interface-level** arithmetization: it does not attempt to define `evaln` inside PA/Q,
it simply exposes it as a symbol interpreted by the standard model `ℕ`.
-/

private def zeroTerm {α : Type} {n : ℕ} : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.zero (fun i => Fin.elim0 i)

private def succTerm {α : Type} {n : ℕ} (t : Lang.Term (α ⊕ Fin n)) : Lang.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.func Func.succ (fun _ => t)

private def numeralTerm {α : Type} {n : ℕ} : ℕ → Lang.Term (α ⊕ Fin n)
  | 0 => zeroTerm
  | m + 1 => succTerm (numeralTerm m)

@[simp] private theorem numeralTerm_realize {α : Type} {n : ℕ} (m : ℕ) (v : α → ℕ) (xs : Fin n → ℕ) :
    (numeralTerm (α := α) (n := n) m).realize (Sum.elim v xs) = m := by
  induction m with
  | zero =>
      simp [numeralTerm, zeroTerm]
  | succ m ih =>
      simp [numeralTerm, succTerm, ih]

/-- Arithmetic halting schema using the `evaln` relation symbol. -/
def H_evaln (e : Code) : Sentence :=
  ∃' ∃'
    (FirstOrder.Language.Relations.boundedFormula (L := Lang) (α := Empty) (l := 2) (n := 4)
      Rel.evaln ![&0, numeralTerm (Nat.Partrec.Code.encodeCode e), numeralTerm 0, &1])

theorem arithmetizesEvaln_H_evaln : ArithmetizesEvaln H_evaln := by
  intro e
  have hDecode : Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode e) = e := by
    simpa [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.encodeCode_eq] using
      (Denumerable.ofNat_encode (α := Code) e)
  -- Unfold truth in the standard model and compute the realization of `H_evaln`.
  -- The only classical input is the standard model-theory lemma interpreting `∃'` (`realize_ex`).
  -- After simp, the only remaining content is simplifying the `Fin.snoc` projections (the two witnesses
  -- are exactly the two bound variables).
  have hSnoc0 {p : Fin 0 → ℕ} {a : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p a 0 = a := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := a) (p := p) (n := 0))
  have hSnoc1 {p : Fin 1 → ℕ} {b : ℕ} :
      Fin.snoc (α := fun _ : Fin 2 => ℕ) p b 1 = b := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 2 => ℕ) (x := b) (p := p) (n := 1))
  -- Main computation: evaluate `H_evaln` in the standard model and simplify the `Fin.snoc` projections.
  simpa [HaltsSigma1] using
    (by
      simp [H_evaln, Truth, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize, hDecode,
        numeralTerm_realize, hSnoc0, hSnoc1])

/--
If `H` arithmetizes `evaln`-halting, then it satisfies the `truth_H` field expected by the
Gödel-I arithmetic interface (`GodelIArith` / `GodelIArithFromChecker`).
-/
theorem truth_H_of_arithmetizesEvaln (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → Sentence) (hH : ArithmetizesEvaln H) :
    ∀ e, Truth (H e) ↔ Rev0_K K (Machine e) := by
  intro e
  exact (hH e).trans (haltsSigma1_iff_rev0_K (K := K) (hK := hK) e)

/--
Σ₁-correctness helper:
if a theory can prove `H e` from a Σ₁ halting witness (`HaltsSigma1 e`),
then it can prove `H e` from `Rev0_K K (Machine e)`.

This is useful because `HaltsSigma1 e` is the *certificate* form (`∃ k x, evaln ...`),
while `Rev0_K` is the RevHalt-level halting predicate used by the Gödel interfaces.
-/
theorem correct_of_correctSigma1 (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → Sentence) (Provable : Sentence → Prop)
    (correctSigma1 : ∀ e, HaltsSigma1 e → Provable (H e)) :
    ∀ e, Rev0_K K (Machine e) → Provable (H e) := by
  intro e hRev
  apply correctSigma1 e
  exact (haltsSigma1_iff_rev0_K (K := K) (hK := hK) e).2 hRev

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.HaltsSigma1
#print axioms RevHalt.Arithmetic.haltsSigma1_iff_rev0_K
#print axioms RevHalt.Arithmetic.reHaltsSigma1
#print axioms RevHalt.Arithmetic.reRev0KMachine
#print axioms RevHalt.Arithmetic.ArithmetizesEvaln
#print axioms RevHalt.Arithmetic.H_evaln
#print axioms RevHalt.Arithmetic.arithmetizesEvaln_H_evaln
#print axioms RevHalt.Arithmetic.truth_H_of_arithmetizesEvaln
#print axioms RevHalt.Arithmetic.correct_of_correctSigma1
