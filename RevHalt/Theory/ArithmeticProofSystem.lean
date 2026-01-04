import RevHalt.Theory.ArithmeticProvability
import RevHalt.Theory.ArithmeticNumerals
import RevHalt.Theory.REPredExtras

/-!
# RevHalt.Theory.ArithmeticProofSystem

RevHalt’s Gödel layer keeps provability abstract. For “Gödel classical” one eventually needs an
**effective provability predicate** for a concrete arithmetic theory.

This file adds the first (interface) brick for that: a *proof checker* viewed as a computable
relation `Sentence → ℕ → Bool`, together with the induced r.e. provability predicate.

Nothing here commits to a specific proof calculus; it only packages the standard reduction:

`Provable φ := ∃ n, Check φ n = true` is recursively enumerable as soon as `Check` is computable.
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

/--
A (syntactic) proof checker for arithmetic sentences.

`Check φ n = true` should mean: “`n` encodes a valid proof of `φ` in the chosen calculus/theory”.

This file only requires *computability* of `Check`, and derives r.e. provability from it.
-/
structure ProofChecker where
  Check : Sentence → ℕ → Bool
  check_computable : Computable₂ Check

namespace ProofChecker

/-- The induced provability predicate: there exists a code `n` accepted by the checker. -/
def Provable (C : ProofChecker) (φ : Sentence) : Prop :=
  ∃ n, C.Check φ n = true

/-- The induced provability predicate is r.e. (recursively enumerable). -/
theorem rePred_Provable (C : ProofChecker) : REPred C.Provable := by
  -- This is just “r.e. is closed under ∃ℕ” applied to the computable checker.
  simpa [ProofChecker.Provable] using
    (RevHalt.rePred_exists_nat_of_computable (α := Sentence) C.Check C.check_computable)

/--
Turn a proof checker into a `ProvabilitySystem`, given consistency/explosion proofs.

This isolates the *effective axiomatizability* requirement (via `rePred_Provable`) from the purely
logical obligations (`consistent`, `absurd`) required by the Gödel lens.
-/
def toProvabilitySystem (C : ProofChecker)
    (consistent : ¬ C.Provable (⊥ : Sentence))
    (absurd : ∀ p : Sentence, C.Provable p → C.Provable p.not → C.Provable (⊥ : Sentence)) :
    ProvabilitySystem where
  Provable := C.Provable
  consistent := consistent
  absurd := absurd

end ProofChecker

end Arithmetic

end RevHalt

