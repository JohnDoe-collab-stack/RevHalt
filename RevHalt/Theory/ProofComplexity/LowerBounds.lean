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
  Constructive direction:
  a super-polynomial lower bound excludes `PolyPosWC`.
-/
theorem SuperPolyLowerBound.not_PolyPosWC
    {PropT : Type}
    (Γ : Set PropT)
    (ChecksDerivation : Set PropT → PropT → ℕ → Bool)
    (ChecksWitness : PropT → List ℕ → Bool)
    (decodeList : ℕ → List ℕ)
    (size : PropT → ℕ)
    (HasSolution : PropT → Prop)
    (hLB : SuperPolyLowerBound Γ ChecksDerivation ChecksWitness decodeList size HasSolution) :
    ¬ Nonempty (PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution) := by
  rintro ⟨hPoly⟩
  rcases hLB hPoly.B hPoly.B_poly with ⟨p, hpSol, hpLB⟩
  rcases hPoly.pos_short p hpSol with ⟨d, hdLt⟩
  exact Nat.not_lt_of_ge (hpLB d) hdLt

end RevHalt.ProofComplexity
