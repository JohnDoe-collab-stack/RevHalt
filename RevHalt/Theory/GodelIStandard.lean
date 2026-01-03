import RevHalt.Theory.GodelLens

/-!
# RevHalt.Theory.GodelIStandard

This file packages the existing Gödel-lens results into a single **Gödel I (standard) interface**.

It does *not* arithmetize PA/Q yet. Instead, it isolates exactly the data one must provide to
instantiate the standard “true but unprovable” conclusion:

1. an internal proof system (`ImpossibleSystem`) with consistency,
2. an external truth semantics `Truth`,
3. a sentence schema `H : Code → PropT` that is true exactly when a code halts (Σ₁ reading),
4. positive correctness: if the code halts, the theory proves `H e`,
5. r.e. refutability: `Provable (¬H e)` is semi-decidable.

From this interface, RevHalt produces:

- a concrete code `e` such that `e` does not halt but `¬H e` is not provable, and
- therefore a sentence that is true but not provable (Gödel I shape).

All non-constructive strength is tracked by axiom audits; this development inherits the fixed-point
machinery dependency from `Mathlib.Computability.PartrecCode` via `T2_impossibility`.
-/

namespace RevHalt

open Nat.Partrec

variable {PropT : Type}

/--
Gödel I (standard) interface for RevHalt.

To instantiate this for PA/Q, `PropT` should be a type of closed arithmetical sentences, `S.Provable`
should be provability in the chosen theory, and `Truth` should be truth in the standard model ℕ.
-/
structure GodelIStandard (PropT : Type) where
  /-- Internal system interface (provability + negation + consistency). -/
  S : ImpossibleSystem PropT
  /-- Canonical kit and its canonicity hypothesis. -/
  K : RHKit
  hK : DetectsMonotone K

  /-- External truth semantics (standard-model truth in the PA/Q instantiation). -/
  Truth : PropT → Prop
  /-- External semantics respects the internal negation symbol. -/
  truth_not : ∀ p, Truth (S.Not p) ↔ ¬ Truth p

  /-- Σ₁-style sentence schema: “`e` halts” as a formula of `PropT`. -/
  H : Code → PropT
  /-- Semantic interpretation of `H` as halting truth. -/
  truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e)

  /-- Positive correctness (Σ₁ completeness of the theory, in the PA/Q instantiation). -/
  correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e)

  /-- Semi-decider for refutability (r.e. `Provable (¬H e)`). -/
  f : Code → (Nat →. Nat)
  f_partrec : Partrec₂ f
  semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)

namespace GodelIStandard

/-- There exists a specific code `e` that does not halt, yet `¬H e` is not provable. -/
theorem exists_nonhalting_unprovable_neg (I : GodelIStandard PropT) :
    ∃ e, ¬ Rev0_K I.K (Machine e) ∧ ¬ I.S.Provable (I.S.Not (I.H e)) := by
  exact
    exists_nonhalting_unprovable_neg_of_correct_semidec
      (S := I.S) (K := I.K) (hK := I.hK)
      (H := I.H) (correct := I.correct)
      (f := I.f) (f_partrec := I.f_partrec) (semidec := I.semidec)

/-- Gödel I standard form: a sentence is true (externally) but not provable (internally). -/
theorem exists_true_unprovable (I : GodelIStandard PropT) :
    ∃ p, I.Truth p ∧ ¬ I.S.Provable p := by
  exact
    godelI_exists_true_unprovable_of_correct_semidec
      (S := I.S) (K := I.K) (hK := I.hK)
      (Truth := I.Truth) (truth_not := I.truth_not)
      (H := I.H) (truth_H := I.truth_H) (correct := I.correct)
      (f := I.f) (f_partrec := I.f_partrec) (semidec := I.semidec)

end GodelIStandard

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.GodelIStandard
#print axioms RevHalt.GodelIStandard.exists_nonhalting_unprovable_neg
#print axioms RevHalt.GodelIStandard.exists_true_unprovable

