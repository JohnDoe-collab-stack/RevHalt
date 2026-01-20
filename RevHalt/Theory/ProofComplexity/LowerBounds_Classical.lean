import RevHalt.Theory.ProofComplexity.LowerBounds

namespace RevHalt.ProofComplexity

open RevHalt.ProofCarrying.Witness
open RevHalt.Complexity

/-!
# Lower Bounds (classical direction)

This file isolates the non-constructive implication:

`¬ Nonempty (PolyPosWC ...)  ->  SuperPolyLowerBound ...`

The reverse direction is constructive and lives in `LowerBounds.lean`.
-/

/--
  Classical direction: if `PolyPosWC` fails (as a global `Nonempty`), then for any candidate
  polynomial bound `B` there is a counterexample `p` whose all WC-derivations exceed `B(size p)`.

  This uses a classical contrapositive step (`by_contra`) to turn `¬ ∃` into `∀ -> ∃`.
-/
theorem not_PolyPosWC_implies_LowerBound
    {PropT : Type}
    (Γ : Set PropT)
    (ChecksDerivation : Set PropT → PropT → ℕ → Bool)
    (ChecksWitness : PropT → List ℕ → Bool)
    (decodeList : ℕ → List ℕ)
    (size : PropT → ℕ)
    (HasSolution : PropT → Prop)
    (hNotPoly : ¬ Nonempty (PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution)) :
    SuperPolyLowerBound Γ ChecksDerivation ChecksWitness decodeList size HasSolution := by
  intro B hB
  -- Contrapositive: if there is no counterexample for B, we can build PolyPosWC with bound B.
  by_contra hNoCounterExample
  rw [not_exists] at hNoCounterExample
  simp only [ge_iff_le, not_and, not_forall, not_le] at hNoCounterExample

  let witness : PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution := {
    B := B
    B_poly := hB
    pos_short := fun p hSol => hNoCounterExample p hSol
  }
  exact hNotPoly (Nonempty.intro witness)

end RevHalt.ProofComplexity

