import RevHalt.Theory.GodelIProofChecker
import RevHalt.Theory.RobinsonQ

/-!
# RevHalt.Theory.GodelIArithmeticQ

This file is a **staging target** for “Gödel classical with Robinson Q”.

RevHalt already has:
- the abstract Gödel-I interface (`GodelIStandard`),
- the arithmetic specialization (`GodelIArith`),
- and a proof-checker-to-Gödel wiring layer (`GodelIArithFromChecker`).

What is still missing for a full Q instantiation is:
- an actual computable proof checker for Q (or a calculus proving Q), and
- an arithmetization of computation `H : Code → Sentence` with `truth_H` and Σ₁-correctness.

This file packages those remaining obligations as one structure and provides the final statement as
an immediate corollary.
-/

namespace RevHalt

namespace Arithmetic

open Nat.Partrec

/--
“Gödel-I over Q”: staging interface for the remaining Q-specific ingredients.

Nothing here proves that the checker corresponds to Q; it only records an optional interface
(`axioms_provable`) expressing that the checker proves the Q axioms.

Once a real proof checker/calculus for Q is implemented, this is the place to instantiate it.
-/
structure GodelIQ where
  /-- Core Gödel-I data sourced from an effective checker (provability r.e.). -/
  I : GodelIArithFromChecker

  /-- Optional: the checker proves each axiom of Robinson arithmetic Q. -/
  axioms_provable : ∀ φ : Sentence, φ ∈ QTheory → I.C.Provable φ

namespace GodelIQ

/-- Gödel-I (Q target): there exists a sentence true in `ℕ` but not provable by the checker. -/
theorem exists_true_unprovable (Q : GodelIQ) :
    ∃ p : Sentence, Truth p ∧ ¬ Q.I.C.Provable p :=
  Q.I.exists_true_unprovable

end GodelIQ

end Arithmetic

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Arithmetic.GodelIQ
#print axioms RevHalt.Arithmetic.GodelIQ.exists_true_unprovable

