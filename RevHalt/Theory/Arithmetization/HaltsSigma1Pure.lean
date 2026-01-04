import RevHalt.Theory.ArithmeticLanguagePure
import RevHalt.Theory.Arithmetization.HaltsSigma1

/-!
# RevHalt.Theory.Arithmetization.HaltsSigma1Pure

This file is the bridge for the “full arithmetization” track:

- `RevHalt.Theory.Arithmetization.HaltsSigma1` defines the computability-level Σ₁ predicate
  `HaltsSigma1 e := ∃ k x, Code.evaln k e 0 = some x` and the interface
  `ArithmetizesEvaln (H : Code → Sentence)`.

- Here we allow the arithmetization to live in the **pure arithmetic sublanguage**
  `Arithmetic.Pure.Lang0` (no extra relations), via a family `H0 : Code → Sentence0`.

We then transport it to the ambient language by `Pure.liftSentence`.
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

namespace Pure

/-- Pure arithmetic arithmetization requirement: `H0` represents Σ₁ `evaln`-halting in `ℕ`. -/
def ArithmetizesEvaln0 (H0 : Code → Sentence0) : Prop :=
  ∀ e, Truth0 (H0 e) ↔ HaltsSigma1 e

/--
Transport: a pure arithmetization `H0` induces an ambient arithmetization
`H := fun e => liftSentence (H0 e)`.
-/
theorem arithmetizesEvaln_of_arithmetizesEvaln0
    (H0 : Code → Sentence0) (h0 : ArithmetizesEvaln0 H0) :
    ArithmetizesEvaln (fun e => liftSentence (H0 e)) := by
  intro e
  exact (truth_liftSentence (φ := H0 e)).trans (h0 e)

/--
If `H0` arithmetizes Σ₁ halting in the pure language, then the lifted `H` satisfies the
`truth_H` field required by the Gödel-I arithmetic interface (`GodelIArith`).
-/
theorem truth_H_of_arithmetizesEvaln0 (K : RHKit) (hK : DetectsMonotone K)
    (H0 : Code → Sentence0) (h0 : ArithmetizesEvaln0 H0) :
    ∀ e, Truth (liftSentence (H0 e)) ↔ Rev0_K K (Machine e) := by
  refine
    truth_H_of_arithmetizesEvaln (K := K) (hK := hK)
      (H := fun e => liftSentence (H0 e))
      (hH := arithmetizesEvaln_of_arithmetizesEvaln0 (H0 := H0) h0)

end Pure

end Arithmetic

end RevHalt

