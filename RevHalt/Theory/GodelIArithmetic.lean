import RevHalt.Theory.GodelIStandard
import RevHalt.Theory.ArithmeticProvability

/-!
# RevHalt.Theory.GodelIArithmetic

This file instantiates the abstract “Gödel I standard” interface (`GodelIStandard`) on:

- `PropT := RevHalt.Arithmetic.Sentence` (first-order arithmetic sentences),
- `Truth :=` satisfaction in the standard model `ℕ`,
- `Not :=` syntactic negation `p.not`, and `FalseT := ⊥`.

What remains abstract (by design) is the **provability predicate** for a concrete arithmetic theory
such as PA or Robinson Q, together with the standard “arithmetization of computation” obligations:

- `H : Code → Sentence` must represent halting (Σ₁ reading),
- positive correctness: `halts e → Provable (H e)`,
- r.e. refutability: `Provable (¬H e)` is semi-decidable.

Given those inputs, RevHalt outputs a sentence true in `ℕ` but not provable in the theory.
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

/-- Data needed to run the Gödel-I standard argument over arithmetic sentences. -/
structure GodelIArith where
  /-- Internal provability interface (to be instantiated by PA/Q/etc.). -/
  T : ProvabilitySystem

  /-- Canonical kit and its canonicity hypothesis. -/
  K : RHKit
  hK : DetectsMonotone K

  /-- Halting schema as an arithmetic sentence. -/
  H : Code → Sentence
  /-- Standard-model reading of `H` as halting. -/
  truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e)
  /-- Positive correctness: halting implies provability of the halting sentence. -/
  correct : ∀ e, Rev0_K K (Machine e) → T.Provable (H e)

  /-- Semi-decider for refutability (r.e. `Provable (¬H e)`). -/
  f : Code → (Nat →. Nat)
  f_partrec : Partrec₂ f
  semidec : ∀ c, T.Provable (H c).not ↔ (∃ x : Nat, x ∈ (f c) 0)

namespace GodelIArith

/-- Package the arithmetic instance into the generic `GodelIStandard` interface. -/
def toGodelIStandard (I : GodelIArith) : RevHalt.GodelIStandard Sentence where
  S := I.T.toImpossibleSystem
  K := I.K
  hK := I.hK
  Truth := Truth
  truth_not := by
    intro p
    simp [ProvabilitySystem.toImpossibleSystem]
  H := I.H
  truth_H := I.truth_H
  correct := I.correct
  f := I.f
  f_partrec := I.f_partrec
  semidec := I.semidec

/-- There exists a code `e` that does not halt, yet `¬H e` is not provable. -/
theorem exists_nonhalting_unprovable_notH (I : GodelIArith) :
    ∃ e, ¬ Rev0_K I.K (Machine e) ∧ ¬ I.T.Provable (I.H e).not := by
  simpa [GodelIArith.toGodelIStandard, ProvabilitySystem.toImpossibleSystem] using
    (RevHalt.GodelIStandard.exists_nonhalting_unprovable_neg (I := I.toGodelIStandard))

/-- Gödel I (standard): there exists a sentence true in `ℕ` but not provable (PA/Q instantiation target). -/
theorem exists_true_unprovable (I : GodelIArith) :
    ∃ p : Sentence, Truth p ∧ ¬ I.T.Provable p := by
  simpa [GodelIArith.toGodelIStandard, ProvabilitySystem.toImpossibleSystem] using
    (RevHalt.GodelIStandard.exists_true_unprovable (I := I.toGodelIStandard))

end GodelIArith

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.GodelIArith
#print axioms RevHalt.Arithmetic.GodelIArith.toGodelIStandard
#print axioms RevHalt.Arithmetic.GodelIArith.exists_nonhalting_unprovable_notH
#print axioms RevHalt.Arithmetic.GodelIArith.exists_true_unprovable
