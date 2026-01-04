import RevHalt.Theory.GodelIArithmetic
import RevHalt.Theory.ArithmeticProofSystem

/-!
# RevHalt.Theory.GodelIProofChecker

This file is a small “wiring” layer for the Gödel track.

`GodelIArithmetic` packages the Gödel-I standard argument over arithmetic sentences, but keeps
the provability predicate abstract (`ProvabilitySystem`).

`ArithmeticProofSystem` provides an *effective* way to obtain an r.e. provability predicate from a
computable proof checker `Check : Sentence → ℕ → Bool`.

Here we connect them:

- from a `ProofChecker` plus `consistent`/`absurd`, we build a `ProvabilitySystem`,
- from computability of the checker, we get `REPred Provable`,
- from `REPred Provable` plus a computable map `c ↦ (H c).not`, we derive the r.e. refutability
  hypothesis needed by `GodelIArith`,
- therefore we can run `GodelIArith.exists_true_unprovable` once `H`, `truth_H`, and `correct` are supplied.

This isolates the remaining hard work for “Gödel classical” to:
1. an actual checker for PA/Q (C1), and
2. the arithmetization bridge `H : Code → Sentence` + correctness (C3/C4).
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

/--
Staging bundle: Gödel-I (standard shape) from an *effective* proof checker.

Compared to `GodelIArith`, this replaces the r.e. refutability semi-decider by the simpler and
standard ingredient “provability is r.e.” (via a computable proof checker), plus a computable map
`c ↦ (H c).not`.
-/
structure GodelIArithFromChecker where
  /-- Proof checker (C1 interface). -/
  C : ProofChecker
  /-- Consistency for the induced provability predicate. -/
  consistent : ¬ C.Provable (⊥ : Sentence)
  /-- Explosion for the induced provability predicate. -/
  absurd : ∀ p : Sentence, C.Provable p → C.Provable p.not → C.Provable (⊥ : Sentence)

  /-- Canonical kit and canonicity hypothesis (RevHalt core). -/
  K : RHKit
  hK : DetectsMonotone K

  /-- Halting schema as an arithmetic sentence (C3). -/
  H : Code → Sentence
  /-- Standard-model reading of `H` as halting (C3). -/
  truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e)
  /-- Positive correctness: halting implies provability of `H e` (C4). -/
  correct : ∀ e, Rev0_K K (Machine e) → C.Provable (H e)

  /-- Computability of the “negated halting” map `c ↦ (H c).not` (needed for C5 packaging). -/
  hNotComp : Computable fun c : Code => (H c).not

namespace GodelIArithFromChecker

/-- The induced `ProvabilitySystem`. -/
def T (I : GodelIArithFromChecker) : ProvabilitySystem :=
  I.C.toProvabilitySystem I.consistent I.absurd

/-- Build the `GodelIArith` package automatically from the checker-based staging data. -/
def toGodelIArith (I : GodelIArithFromChecker) : GodelIArith := by
  -- r.e. provability comes directly from the checker.
  have reProvable : REPred (I.T.Provable) := by
    -- `I.T.Provable` is definitionally `I.C.Provable`.
    simpa [GodelIArithFromChecker.T, ProofChecker.toProvabilitySystem] using I.C.rePred_Provable
  -- Use the generic constructor which derives r.e. refutability automatically.
  exact
    GodelIArith.mk_of_REPred
      (T := I.T)
      (reProvable := reProvable)
      (K := I.K) (hK := I.hK)
      (H := I.H) (truth_H := I.truth_H)
      (correct := fun e he => I.correct e he)
      (hNotComp := I.hNotComp)

/-- Gödel-I (standard): there exists an arithmetic sentence true in `ℕ` but not provable. -/
theorem exists_true_unprovable (I : GodelIArithFromChecker) :
    ∃ p : Sentence, Truth p ∧ ¬ I.C.Provable p := by
  have h := (GodelIArith.exists_true_unprovable (I := I.toGodelIArith))
  -- Unfold the induced provability predicate back to `I.C.Provable`.
  simpa [GodelIArithFromChecker.toGodelIArith, GodelIArithFromChecker.T, ProofChecker.toProvabilitySystem] using h

end GodelIArithFromChecker

/--
Variant staging bundle: Gödel-I from an effective checker **plus an explicit r.e. refutability
semi-decider** for `Provable (¬(H c))`.

This removes the extra “syntactic map computability” obligation `Computable (fun c => (H c).not)`.
It is strictly weaker than `GodelIArithFromChecker`: the refutability semi-decider is provided as
data (a `RECodePred`) rather than derived automatically.
-/
structure GodelIArithFromCheckerRE where
  /-- Proof checker (C1 interface). -/
  C : ProofChecker
  /-- Consistency for the induced provability predicate. -/
  consistent : ¬ C.Provable (⊥ : Sentence)
  /-- Explosion for the induced provability predicate. -/
  absurd : ∀ p : Sentence, C.Provable p → C.Provable p.not → C.Provable (⊥ : Sentence)

  /-- Canonical kit and canonicity hypothesis (RevHalt core). -/
  K : RHKit
  hK : DetectsMonotone K

  /-- Halting schema as an arithmetic sentence (C3). -/
  H : Code → Sentence
  /-- Standard-model reading of `H` as halting (C3). -/
  truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e)
  /-- Positive correctness: halting implies provability of `H e` (C4). -/
  correct : ∀ e, Rev0_K K (Machine e) → C.Provable (H e)

  /-- r.e. refutability: semi-decider for `C.Provable (¬(H c))` (C5). -/
  reNotH : RECodePred fun c => C.Provable (H c).not

namespace GodelIArithFromCheckerRE

/-- The induced `ProvabilitySystem`. -/
def T (I : GodelIArithFromCheckerRE) : ProvabilitySystem :=
  I.C.toProvabilitySystem I.consistent I.absurd

/-- Build the `GodelIArith` package from the checker + explicit `RECodePred` refutability data. -/
def toGodelIArith (I : GodelIArithFromCheckerRE) : GodelIArith := by
  refine
    { T := I.T
      K := I.K
      hK := I.hK
      H := I.H
      truth_H := I.truth_H
      correct := fun e he => I.correct e he
      f := I.reNotH.f
      f_partrec := I.reNotH.f_partrec
      semidec := ?_ }
  intro c
  -- `I.T.Provable` is definitionally `I.C.Provable`.
  simpa [GodelIArithFromCheckerRE.T, ProofChecker.toProvabilitySystem] using (I.reNotH.spec c)

/-- Gödel-I (standard): there exists an arithmetic sentence true in `ℕ` but not provable. -/
theorem exists_true_unprovable (I : GodelIArithFromCheckerRE) :
    ∃ p : Sentence, Truth p ∧ ¬ I.C.Provable p := by
  have h := (GodelIArith.exists_true_unprovable (I := I.toGodelIArith))
  simpa [GodelIArithFromCheckerRE.toGodelIArith, GodelIArithFromCheckerRE.T,
    ProofChecker.toProvabilitySystem] using h

end GodelIArithFromCheckerRE

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.GodelIArithFromChecker
#print axioms RevHalt.Arithmetic.GodelIArithFromChecker.T
#print axioms RevHalt.Arithmetic.GodelIArithFromChecker.toGodelIArith
#print axioms RevHalt.Arithmetic.GodelIArithFromChecker.exists_true_unprovable

#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerRE
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerRE.T
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerRE.toGodelIArith
#print axioms RevHalt.Arithmetic.GodelIArithFromCheckerRE.exists_true_unprovable
