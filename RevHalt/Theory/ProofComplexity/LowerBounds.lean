/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds

namespace RevHalt.ProofComplexity

open RevHalt.ProofCarrying.Witness
open RevHalt.Complexity

/--
  **Super-Polynomial Lower Bound**:
  A system exhibits super-polynomial lower bounds if for *every* polynomial bound `B`,
  there exists a true instance `p` such that *all* valid witness-carrying derivations `d` for `p`
  have code size at least `B (size p)`.

  This is the formal negation of `PolyPosWC`.
-/
def SuperPolyLowerBound
    {PropT : Type}
    (Γ : Set PropT)
    (ChecksDerivation : Set PropT → PropT → ℕ → Bool)
    (ChecksWitness : PropT → List ℕ → Bool)
    (decodeList : ℕ → List ℕ)
    (size : PropT → ℕ)
    (HasSolution : PropT → Prop)
    : Prop :=
  ∀ B : ℕ → ℕ, IsPoly B →
    ∃ p, HasSolution p ∧
      ∀ d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p,
        d.code ≥ B (size p)

/--
  **Theorem 3 (Metatheoretic Implication)**:
  If a system does NOT satisfy `PolyPosWC` (i.e., short proofs do not exist for all true statements),
  then it satisfies `SuperPolyLowerBound`.

  This is essentially constructive logic: if we cannot construct a polynomial bounding function,
  it means for any candidate polynomial, there is a counter-example.
  Note: This requires classical logic for the direction `¬ ∀ ... → ∃ ...`.
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
  -- We assume for contradiction that NO such p exists (i.e. all p have short proofs for THIS B).
  -- Then we can construct a PolyPosWC with this B, contradicting hNotPoly.
  -- To do this classically:
  by_contra hNoCounterExample
  -- hNoCounterExample : ¬ ∃ p, HasSolution p ∧ ∀ d, d.code ≥ B (size p)
  -- <=> ∀ p, ¬ (HasSolution p ∧ ∀ d, d.code ≥ B (size p))
  -- <=> ∀ p, HasSolution p → ¬ (∀ d, d.code ≥ B (size p))
  -- <=> ∀ p, HasSolution p → ∃ d, d.code < B (size p)
  rw [not_exists] at hNoCounterExample
  simp only [ge_iff_le, not_and, not_forall, not_le] at hNoCounterExample

  -- Create the PolyPosWC instance
  let witness : PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution := {
    B := B,
    B_poly := hB,
    pos_short := fun p hSol => hNoCounterExample p hSol
  }
  exact hNotPoly (Nonempty.intro witness)

end RevHalt.ProofComplexity
