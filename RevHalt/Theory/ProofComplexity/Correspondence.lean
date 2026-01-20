/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds

/-!
# Correspondence with Proof Complexity

This module establishes the formal connection between the RevHalt framework's
`PolyPosWC` (witness-carrying complexity) and standard **Propositional Proof Systems (PPS)**
in the sense of Cook and Reckhow.

## Main Definitions

* `PropositionalProofSystem`: A computable function `V : PropT → Proof → Bool` that is sound
  and complete for a language.
* `PolynomiallyBoundedPPS`: A PPS where every true statement has a proof of polynomial size.
* `toPPS`: Canonical construction of a PPS from a `ChecksWC` instance.
* `Correspondence`: Theorem stating that `PolyPosWC` is equivalent to the existence of a
  polynomially bounded PPS derived from the witness checker.

-/

namespace RevHalt.ProofComplexity

open RevHalt.ProofCarrying.Witness
open RevHalt.Complexity

variable {PropT : Type}

/--
  A standard **Propositional Proof System (PPS)** for a validity predicate `IsTautology`.
  It consists of a computable verifier `V` that checks if `π` is a proof of `x`.

  Technically, Cook-Reckhow defines a PPS as a surjective poly-time function `f : Σ* -> TAUT`.
  Here we use the "verifier" view: `V(x, π)` accepts iff `f(π) = x`.
-/
structure PropositionalProofSystem
    (IsTautology : PropT → Prop)
    (Proof : Type)
    (sizeProof : Proof → ℕ) where
  /-- The Verifier function. -/
  Verifier : PropT → Proof → Bool
  /-- Soundness: If the verifier accepts, the statement is true. -/
  sound : ∀ x π, Verifier x π = true → IsTautology x
  /-- Completeness: If the statement is true, there exists a proof accepted by the verifier. -/
  complete : ∀ x, IsTautology x → ∃ π, Verifier x π = true

/--
  A PPS is **Polynomially Bounded** if there is a polynomial `p` such that
  every tautology `x` has a proof `π` with `size(π) ≤ p(size(x))`.
-/
structure PolynomiallyBoundedPPS
    {IsTautology : PropT → Prop}
    {Proof : Type}
    {sizeProof : Proof → ℕ}
    (Sys : PropositionalProofSystem IsTautology Proof sizeProof)
    (sizeProp : PropT → ℕ) : Type where
  /-- The bounding polynomial. -/
  P : ℕ → ℕ
  /-- It is a polynomial. -/
  is_poly : IsPoly P
  /-- Short proofs exist. -/
  short_proofs : ∀ x, IsTautology x → ∃ π, Sys.Verifier x π = true ∧ sizeProof π ≤ P (sizeProp x)

section Correspondence

variable (Γ : Set PropT)
variable (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)
variable (ChecksWitness : PropT → List ℕ → Bool)
variable (decodeList : ℕ → List ℕ)
variable (size : PropT → ℕ)
variable (HasSolution : PropT → Prop)


/--
  **Construction**: Every `ChecksWC` system induces a Propositional Proof System.
  The "Proof" is the `WCCode` (encoding both derivation and witness).
-/
def toPPS
    (hSound : ∀ p, (∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c) → HasSolution p)
    (hComplete : ∀ p, HasSolution p → ∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c) -- Added completeness assumption
    : PropositionalProofSystem HasSolution WCCode id := {
  Verifier := fun p c => ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c
  sound := fun p c hCheck => hSound p ⟨c, hCheck⟩
  complete := fun p hSol => hComplete p hSol
}

/--
  **Theorem (Direction 1)**: If `PolyPosWC` holds, then the induced PPS is polynomially bounded.
-/
def PolyPosWC_implies_PolyPPS
    (hSound : ∀ p, (∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c) → HasSolution p)
    (hComplete : ∀ p, HasSolution p → ∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c)
    (hPoly : PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution) :
    PolynomiallyBoundedPPS (toPPS Γ ChecksDerivation ChecksWitness decodeList HasSolution hSound hComplete) size := {
  P := hPoly.B
  is_poly := hPoly.B_poly
  short_proofs := fun p hSol => by
    refine Exists.elim (hPoly.pos_short p hSol) (fun d hd_bound => ?_)
    -- d is WCDerivation, d.code is the proof
    apply Exists.intro d.code
    constructor
    · exact d.valid
    · exact Nat.le_of_lt hd_bound
}

/-- Helper: P(n) is poly => P(n) + 1 is poly -/
lemma IsPoly_succ (f : ℕ → ℕ) (h : IsPoly f) : IsPoly (fun n => f n + 1) := by
  unfold IsPoly at h
  refine Exists.elim h (fun c hc => ?_)
  refine Exists.elim hc (fun d h_bound => ?_)
  unfold IsPoly
  apply Exists.intro (c + 1)
  apply Exists.intro d
  intro n
  calc
    f n + 1 ≤ (c * n^d + c) + 1 := Nat.add_le_add_right (h_bound n) 1
    _       = c * n^d + c + 1   := rfl
    _       = c * n^d + (c + 1) := Nat.add_assoc _ _ _
    _       ≤ (c + 1) * n^d + (c + 1) := by
      apply Nat.add_le_add_right
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.le_add_right _ _

/--
  **Theorem (Direction 2)**: If the induced PPS is polynomially bounded, then `PolyPosWC` holds.
-/
def PolyPPS_implies_PolyPosWC
    (hSound : ∀ p, (∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c) → HasSolution p)
    (hComplete : ∀ p, HasSolution p → ∃ c, ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c)
    (hPPS : PolynomiallyBoundedPPS (toPPS Γ ChecksDerivation ChecksWitness decodeList HasSolution hSound hComplete) size) :
    PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution := {
  B := fun n => hPPS.P n + 1
  B_poly := IsPoly_succ hPPS.P hPPS.is_poly
  pos_short := fun p hSol => by
    refine Exists.elim (hPPS.short_proofs p hSol) (fun c hc => ?_)
    have hCheck := hc.1
    have hSize := hc.2
    -- Construct the derivation inline
    apply Exists.intro { code := c, valid := hCheck }
    -- The Code field is c. Bound is P + 1. c <= P.
    exact Nat.lt_succ_of_le hSize
}

end Correspondence

end RevHalt.ProofComplexity
