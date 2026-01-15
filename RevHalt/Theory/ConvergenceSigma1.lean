import RevHalt.Theory.ThreeBlocksArchitecture

/-!
# RevHalt.Theory.ConvergenceSigma1

This file isolates a small but important computational fact used by the Gödel track:

`Converges e` (halting of a `Nat.Partrec.Code`) is a Σ₁-style property, because `eval` is
approximated by the bounded evaluator `evaln`.

Concretely:

`Converges e ↔ ∃ k x, evaln k e 0 = some x`.

This is the form typically targeted when arithmetizing halting as a Σ₁ arithmetic sentence.

Audit note: in the current mathlib development, the key lemma
`Nat.Partrec.Code.evaln_complete` depends on `Classical.choice`, so the Σ₁ equivalences in this file
inherit that axiom (see the `#print axioms` output at the end).
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

/--
For a monotone kit, `Rev0_K K (Machine e)` is Σ₁ via `evaln`.

This is the exact “arithmetization target shape” used by the Gödel track:
`Rev0_K` on machine codes reduces to a single existential witness.
-/
theorem rev0_K_machine_iff_exists_evaln (K : RHKit) (hK : DetectsUpFixed K) (e : Code) :
    Rev0_K K (Machine e) ↔ ∃ k x, Nat.Partrec.Code.evaln k e 0 = some x := by
  have hT1 : Rev0_K K (Machine e) ↔ Halts (Machine e) :=
    T1_traces K hK (Machine e)
  have hHalts : Halts (Machine e) ↔ (∃ x : Nat, x ∈ e.eval 0) :=
    Halts_Machine_iff e
  have hSigma1 : (∃ x : Nat, x ∈ e.eval 0) ↔ ∃ k x, Nat.Partrec.Code.evaln k e 0 = some x := by
    constructor
    · rintro ⟨x, hx⟩
      rcases (Nat.Partrec.Code.evaln_complete (c := e) (n := 0) (x := x)).1 hx with ⟨k, hk⟩
      exact ⟨k, x, hk⟩
    · rintro ⟨k, x, hk⟩
      exact ⟨x, (Nat.Partrec.Code.evaln_complete (c := e) (n := 0) (x := x)).2 ⟨k, hk⟩⟩
  exact hT1.trans (hHalts.trans hSigma1)

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.converges_iff_exists_evaln
#print axioms RevHalt.rev0_K_machine_iff_exists_evaln
