import RevHalt.Theory.GodelIProofChecker
import RevHalt.Theory.Arithmetization.HaltsSigma1

/-!
# RevHalt.Theory.GodelIProofCheckerEvaln

This is a small convenience layer for the Gödel track.

`GodelIProofChecker` expects a halting schema `H : Code → Sentence` together with
`truth_H : Truth (H e) ↔ Rev0_K K (Machine e)`, and a correctness field stated at the `Rev0_K` level.

When working toward “Gödel classical”, the natural intermediate interface is instead:

- `ArithmetizesEvaln H` : `Truth (H e) ↔ HaltsSigma1 e`, where `HaltsSigma1 e := ∃ k x, evaln k e 0 = some x`,
- Σ₁-correctness stated against the witness predicate `HaltsSigma1`.

This file packages those two bridge steps:

- `truth_H` is derived from `ArithmetizesEvaln` via `truth_H_of_arithmetizesEvaln`,
- `Rev0_K`-level correctness is derived from Σ₁ correctness via `correct_of_correctSigma1`.

It mirrors `GodelIProofChecker` by providing:
- a default variant that derives r.e. refutability from r.e. provability + a computable `c ↦ (H c).not`, and
- an `…RE` variant where r.e. refutability is supplied explicitly (avoiding the extra computability obligation).
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

/--
Gödel-I from an effective proof checker, but with the halting interface stated at the Σ₁ `evaln`
level (`HaltsSigma1`).
-/
structure GodelIArithFromCheckerEvaln where
  /-- Proof checker (effective provability). -/
  C : ProofChecker
  /-- Consistency for the induced provability predicate. -/
  consistent : ¬ C.Provable (⊥ : Sentence)
  /-- Explosion for the induced provability predicate. -/
  absurd : ∀ p : Sentence, C.Provable p → C.Provable p.not → C.Provable (⊥ : Sentence)

  /-- Canonical kit and its canonicity hypothesis (RevHalt core). -/
  K : RHKit
  hK : DetectsMonotone K

  /-- Halting schema as an arithmetic sentence. -/
  H : Code → Sentence
  /-- Arithmetic arithmetization: `H` represents Σ₁ `evaln`-halting in `ℕ`. -/
  arith : ArithmetizesEvaln H
  /-- Σ₁ correctness: a halting witness yields a proof of `H e`. -/
  correctSigma1 : ∀ e, HaltsSigma1 e → C.Provable (H e)

  /-- Computability of the “negated halting” map `c ↦ (H c).not`. -/
  hNotComp : Computable fun c : Code => (H c).not

namespace GodelIArithFromCheckerEvaln

/-- Convert Σ₁-stated data into the standard checker-based Gödel-I staging bundle. -/
def toGodelIArithFromChecker (I : GodelIArithFromCheckerEvaln) : GodelIArithFromChecker where
  C := I.C
  consistent := I.consistent
  absurd := I.absurd
  K := I.K
  hK := I.hK
  H := I.H
  truth_H := truth_H_of_arithmetizesEvaln (K := I.K) (hK := I.hK) (H := I.H) I.arith
  correct :=
    correct_of_correctSigma1 (K := I.K) (hK := I.hK) (H := I.H) (Provable := I.C.Provable)
      I.correctSigma1
  hNotComp := I.hNotComp

/-- Gödel-I (standard): there exists an arithmetic sentence true in `ℕ` but not provable. -/
theorem exists_true_unprovable (I : GodelIArithFromCheckerEvaln) :
    ∃ p : Sentence, Truth p ∧ ¬ I.C.Provable p :=
  (I.toGodelIArithFromChecker).exists_true_unprovable

end GodelIArithFromCheckerEvaln

/--
Variant staging bundle: Σ₁/evaln version of `GodelIArithFromCheckerRE`.

This removes the extra “syntactic map computability” obligation
`Computable (fun c => (H c).not)` by taking r.e. refutability as explicit data.
-/
structure GodelIArithFromCheckerEvalnRE where
  /-- Proof checker (effective provability). -/
  C : ProofChecker
  /-- Consistency for the induced provability predicate. -/
  consistent : ¬ C.Provable (⊥ : Sentence)
  /-- Explosion for the induced provability predicate. -/
  absurd : ∀ p : Sentence, C.Provable p → C.Provable p.not → C.Provable (⊥ : Sentence)

  /-- Canonical kit and its canonicity hypothesis (RevHalt core). -/
  K : RHKit
  hK : DetectsMonotone K

  /-- Halting schema as an arithmetic sentence. -/
  H : Code → Sentence
  /-- Arithmetic arithmetization: `H` represents Σ₁ `evaln`-halting in `ℕ`. -/
  arith : ArithmetizesEvaln H
  /-- Σ₁ correctness: a halting witness yields a proof of `H e`. -/
  correctSigma1 : ∀ e, HaltsSigma1 e → C.Provable (H e)

  /-- r.e. refutability: semi-decider for `C.Provable (¬(H c))`. -/
  reNotH : RECodePred fun c => C.Provable (H c).not

namespace GodelIArithFromCheckerEvalnRE

/-- Convert Σ₁-stated data into the standard `…FromCheckerRE` bundle. -/
def toGodelIArithFromCheckerRE (I : GodelIArithFromCheckerEvalnRE) : GodelIArithFromCheckerRE where
  C := I.C
  consistent := I.consistent
  absurd := I.absurd
  K := I.K
  hK := I.hK
  H := I.H
  truth_H := truth_H_of_arithmetizesEvaln (K := I.K) (hK := I.hK) (H := I.H) I.arith
  correct :=
    correct_of_correctSigma1 (K := I.K) (hK := I.hK) (H := I.H) (Provable := I.C.Provable)
      I.correctSigma1
  reNotH := I.reNotH

/-- Gödel-I (standard): there exists an arithmetic sentence true in `ℕ` but not provable. -/
theorem exists_true_unprovable (I : GodelIArithFromCheckerEvalnRE) :
    ∃ p : Sentence, Truth p ∧ ¬ I.C.Provable p :=
  (I.toGodelIArithFromCheckerRE).exists_true_unprovable

end GodelIArithFromCheckerEvalnRE

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvaln
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvaln.toGodelIArithFromChecker
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvaln.exists_true_unprovable

#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvalnRE
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvalnRE.toGodelIArithFromCheckerRE
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerEvalnRE.exists_true_unprovable
