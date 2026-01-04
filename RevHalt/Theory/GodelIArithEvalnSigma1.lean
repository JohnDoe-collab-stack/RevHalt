import RevHalt.Theory.GodelIArithmetic
import RevHalt.Theory.Arithmetization.HaltsSigma1

namespace RevHalt

namespace Arithmetic

open Nat.Partrec
open FirstOrder
open scoped FirstOrder

/-!
# RevHalt.Theory.GodelIArithEvalnSigma1

This file provides a **fully concrete** end-to-end instantiation of the Gödel-I arithmetic pipeline
using the Σ₁ `evaln`-halting schema `H_evaln`.

It deliberately keeps “provability” minimal: the provability predicate proves exactly those
sentences of the form `H_evaln e` for which a Σ₁ halting witness exists.

This is not “PA/Q provability”; it is a staging theory that demonstrates the RevHalt machine:

- arithmetize halting as a sentence schema (`H_evaln`),
- assume only positive Σ₁ correctness and r.e. refutability of `¬H`,
- derive a sentence true in `ℕ` but not provable.

For “Gödel classical (Q/PA)”, replace this provability predicate by an actual proof checker and keep
`H_evaln` as the arithmetization interface.
-/

/-- A canonical kit: projection is plain existence. -/
def KStd : RHKit :=
  ⟨fun X => ∃ n, X n⟩

theorem detectsMonotone_KStd : DetectsMonotone KStd := by
  intro X _hX
  rfl

/-! ## A minimal Σ₁ provability predicate for the halting schema -/

/-- “Provable” means: the sentence *is* some `H_evaln e`, and `e` has a Σ₁ halting witness. -/
def ProvableSigma1 (φ : Sentence) : Prop :=
  ∃ e, φ = H_evaln e ∧ HaltsSigma1 e

theorem bot_ne_H_evaln (e : Code) : (⊥ : Sentence) ≠ H_evaln e := by
  simp [H_evaln, FirstOrder.Language.BoundedFormula.ex, FirstOrder.Language.BoundedFormula.not]

theorem not_H_evaln_ne_H_evaln (c e : Code) : (H_evaln c).not ≠ H_evaln e := by
  simp [H_evaln, FirstOrder.Language.BoundedFormula.ex, FirstOrder.Language.BoundedFormula.not]

/-- The induced `ProvabilitySystem` (consistency + explosion), for the Σ₁ provability predicate. -/
def Sigma1ProvabilitySystem : ProvabilitySystem where
  Provable := ProvableSigma1
  consistent := by
    intro h
    rcases h with ⟨e, hEq, _hHalts⟩
    exact (bot_ne_H_evaln e) hEq
  absurd := by
    intro p hp hnp
    rcases hp with ⟨e, rfl, _hHalts⟩
    rcases hnp with ⟨e', hEq, _hHalts'⟩
    exact False.elim ((not_H_evaln_ne_H_evaln e e') hEq)

/-! ## r.e. refutability package (trivial: `¬H` is never provable here) -/

/-- A semi-decider that never halts (for the always-false predicate). -/
def neverHalts : Code → (Nat →. Nat) :=
  fun _c => fun _n => Part.none

theorem neverHalts_partrec : Partrec₂ neverHalts := by
  unfold Partrec₂
  simpa [neverHalts] using (Partrec.none : Partrec (fun _ : Code × Nat => (Part.none : Part Nat)))

theorem provableSigma1_notH_false (c : Code) :
    ¬ Sigma1ProvabilitySystem.Provable (H_evaln c).not := by
  intro h
  rcases h with ⟨e, hEq, _hHalts⟩
  exact (not_H_evaln_ne_H_evaln c e) hEq

/-! ## Concrete `GodelIArith` instance -/

/-- The concrete Gödel-I arithmetic instance (Σ₁/evaln halting schema + Σ₁ provability). -/
def GodelIArithEvalnSigma1 : GodelIArith where
  T := Sigma1ProvabilitySystem
  K := KStd
  hK := detectsMonotone_KStd
  H := H_evaln
  truth_H :=
    truth_H_of_arithmetizesEvaln
      (K := KStd) (hK := detectsMonotone_KStd)
      (H := H_evaln)
      arithmetizesEvaln_H_evaln
  correct := by
    intro e hRev
    refine ⟨e, rfl, ?_⟩
    exact (haltsSigma1_iff_rev0_K (K := KStd) (hK := detectsMonotone_KStd) e).2 hRev
  f := neverHalts
  f_partrec := neverHalts_partrec
  semidec := by
    intro c
    constructor
    · intro h
      exact False.elim ((provableSigma1_notH_false c) h)
    · rintro ⟨x, hx⟩
      -- `neverHalts c 0 = Part.none`, so membership is impossible.
      simp [neverHalts] at hx

/-- Gödel-I (explicit `¬H` form): there exists `e` with `¬Halts` and `¬Provable (¬H e)`. -/
theorem exists_nonhalting_unprovable_notH_evalnSigma1 :
    ∃ e, ¬ Rev0_K KStd (Machine e) ∧ ¬ Sigma1ProvabilitySystem.Provable (H_evaln e).not := by
  simpa [GodelIArithEvalnSigma1, Sigma1ProvabilitySystem, ProvableSigma1, KStd, detectsMonotone_KStd] using
    (GodelIArith.exists_nonhalting_unprovable_notH (I := GodelIArithEvalnSigma1))

/-- Gödel-I (standard): there exists an arithmetic sentence true in `ℕ` but not provable. -/
theorem exists_true_unprovable_evalnSigma1 :
    ∃ p : Sentence, Truth p ∧ ¬ Sigma1ProvabilitySystem.Provable p := by
  simpa [GodelIArithEvalnSigma1, Sigma1ProvabilitySystem, ProvableSigma1, KStd, detectsMonotone_KStd] using
    (GodelIArith.exists_true_unprovable (I := GodelIArithEvalnSigma1))

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.Sigma1ProvabilitySystem
#print axioms RevHalt.Arithmetic.GodelIArithEvalnSigma1
#print axioms RevHalt.Arithmetic.exists_nonhalting_unprovable_notH_evalnSigma1
#print axioms RevHalt.Arithmetic.exists_true_unprovable_evalnSigma1
