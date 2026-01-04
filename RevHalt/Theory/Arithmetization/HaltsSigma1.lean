import RevHalt.Theory.ConvergenceSigma1
import RevHalt.Theory.ArithmeticLanguage

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

/-- The Σ₁ halting predicate on codes: halting is witnessed by a bounded evaluation. -/
def HaltsSigma1 (e : Code) : Prop :=
  ∃ k x, Nat.Partrec.Code.evaln k e 0 = some x

/-- `HaltsSigma1` is exactly `Rev0_K K (Machine e)` for a monotone kit. -/
theorem haltsSigma1_iff_rev0_K (K : RHKit) (hK : DetectsMonotone K) (e : Code) :
    HaltsSigma1 e ↔ Rev0_K K (Machine e) := by
  simpa [HaltsSigma1] using (RevHalt.rev0_K_machine_iff_exists_evaln (K := K) (hK := hK) e).symm

/--
Arithmetic-level arithmetization requirement for halting:
`H` represents the Σ₁ predicate `HaltsSigma1` in the standard model.
-/
def ArithmetizesEvaln (H : Code → Sentence) : Prop :=
  ∀ e, Truth (H e) ↔ HaltsSigma1 e

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
#print axioms RevHalt.Arithmetic.ArithmetizesEvaln
#print axioms RevHalt.Arithmetic.truth_H_of_arithmetizesEvaln
#print axioms RevHalt.Arithmetic.correct_of_correctSigma1
