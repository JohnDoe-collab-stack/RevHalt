import RevHalt.Theory.ThreeBlocksArchitecture

/-!
# RevHalt.Theory.ConvergenceSigma1

This file isolates a small but important computational fact used by the Gödel track:

`Converges e` (halting of a `Nat.Partrec.Code`) is a Σ₁-style property, because `eval` is
approximated by the bounded evaluator `evaln`.

Concretely:

`Converges e ↔ ∃ k x, evaln k e 0 = some x`.

This is the form typically targeted when arithmetizing halting as a Σ₁ arithmetic sentence.
-/

namespace RevHalt

open Nat.Partrec

/-- `Converges` is Σ₁ via `evaln`: it holds iff some bounded evaluation returns an output. -/
theorem converges_iff_exists_evaln (e : Code) :
    Converges e ↔ ∃ k x, Nat.Partrec.Code.evaln k e 0 = some x := by
  -- Unfold `Converges` and use `evaln_complete` from `Mathlib.Computability.PartrecCode`.
  dsimp [Converges]
  constructor
  · rintro ⟨x, hx⟩
    rcases (Nat.Partrec.Code.evaln_complete (c := e) (n := 0) (x := x)).1 hx with ⟨k, hk⟩
    exact ⟨k, x, hk⟩
  · rintro ⟨k, x, hk⟩
    exact ⟨x, (Nat.Partrec.Code.evaln_complete (c := e) (n := 0) (x := x)).2 ⟨k, hk⟩⟩

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.converges_iff_exists_evaln

