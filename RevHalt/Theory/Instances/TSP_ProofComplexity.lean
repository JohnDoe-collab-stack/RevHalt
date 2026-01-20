import RevHalt.Theory.ProofComplexity.Correspondence
import RevHalt.Theory.Instances.TSP_Canonization

namespace RevHalt.TSP

open RevHalt.ProofCarrying.Witness

/-!
# TSP ↔ Proof Complexity (PPS) Correspondence

This module instantiates `RevHalt.ProofComplexity` for the concrete TSP checker.

Key output (objective A): a direct, constructive endpoint

`PolyPosWC_TSP ChecksDerivation ωΓ -> PolynomiallyBoundedPPS (TSP_PPS ...) TSPSize`.

No `noncomputable`, no `classical`.
-/

/-- Soundness: if the WC checker accepts, then the instance is true (`IsTrue_TSP`). -/
theorem IsTrue_TSP_of_ChecksWC
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ) :
    ∀ p,
      (∃ c, ChecksWC ChecksDerivation ChecksWitness_TSP decodeList Γ p c) →
      IsTrue_TSP p := by
  intro p h
  rcases h with ⟨c, hCheck⟩
  have hCheck' : ChecksWC ChecksDerivation ChecksWitness_TSP decodeList Γ p c = true := by
    simpa using hCheck
  have hValid := hCheck'
  unfold ChecksWC at hValid
  simp only [Bool.and_eq_true] at hValid
  have hWitnessCheck : ChecksWitness_TSP p (decodeWitness decodeList c) = true := hValid.2
  cases hdec : decodeTSP p with
  | none =>
      have : False := by
        simp [ChecksWitness_TSP, hdec] at hWitnessCheck
      exact False.elim this
  | some inst =>
      have hCheckTour : checkTour inst (decodeWitness decodeList c) = true := by
        simpa [ChecksWitness_TSP, hdec] using hWitnessCheck
      rcases checkTour_sound inst (decodeWitness decodeList c) hCheckTour with ⟨tour, _, hValidTour⟩
      exact ⟨inst, hdec, ⟨tour, hValidTour⟩⟩

/-- Completeness of `ChecksWC` derived from `PolyPosWC_TSP` (a fortiori, from short WC proofs). -/
theorem ChecksWC_complete_of_PolyPosWC_TSP
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ)
    (hPoly : PolyPosWC_TSP ChecksDerivation Γ) :
    ∀ p, IsTrue_TSP p → ∃ c, ChecksWC ChecksDerivation ChecksWitness_TSP decodeList Γ p c := by
  intro p hTrue
  rcases hPoly.pos_short p hTrue with ⟨d, _hBound⟩
  exact ⟨d.code, d.valid⟩

/-- The induced PPS for TSP, parameterized by an explicit completeness proof. -/
def TSP_PPS
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ)
    (hComplete : ∀ p, IsTrue_TSP p → ∃ c, ChecksWC ChecksDerivation ChecksWitness_TSP decodeList Γ p c) :
    RevHalt.ProofComplexity.PropositionalProofSystem IsTrue_TSP WCCode id :=
  RevHalt.ProofComplexity.toPPS
    (Γ := Γ)
    (ChecksDerivation := ChecksDerivation)
    (ChecksWitness := ChecksWitness_TSP)
    (decodeList := decodeList)
    (HasSolution := IsTrue_TSP)
    (hSound := IsTrue_TSP_of_ChecksWC (ChecksDerivation := ChecksDerivation) Γ)
    (hComplete := hComplete)

/--
Main endpoint (objective A, concrete):
`PolyPosWC_TSP` implies existence of polynomially bounded PPS proofs
for the induced verifier (based on `ChecksWC`).
-/
def PolyPosWC_TSP_implies_PolyPPS
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ)
    (hPoly : PolyPosWC_TSP ChecksDerivation Γ) :
    RevHalt.ProofComplexity.PolynomiallyBoundedPPS
      (TSP_PPS ChecksDerivation Γ
        (ChecksWC_complete_of_PolyPosWC_TSP (ChecksDerivation := ChecksDerivation) Γ hPoly))
      TSPSize :=
  RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS
    (Γ := Γ)
    (ChecksDerivation := ChecksDerivation)
    (ChecksWitness := ChecksWitness_TSP)
    (decodeList := decodeList)
    (size := TSPSize)
    (HasSolution := IsTrue_TSP)
    (hSound := IsTrue_TSP_of_ChecksWC (ChecksDerivation := ChecksDerivation) Γ)
    (hComplete := ChecksWC_complete_of_PolyPosWC_TSP (ChecksDerivation := ChecksDerivation) Γ hPoly)
    (hPoly := hPoly)

/--
Objective A (end-to-end, constructive):
`S1Rel = ∅` at `omegaΓ` + `PolyCompressionWC_TSP` ⇒ a polynomially bounded PPS for TSP,
under an explicit decidability hypothesis on WC-provability at `omegaΓ`.
-/
def PolyCompressionWC_TSP_of_Stable_of_decidable_implies_PolyPPS
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (omegaΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hDec : DecidablePred (fun p => Provable_TSP_WC (ChecksDerivation := ChecksDerivation) omegaΓ p))
    (hEmpty :
      S1Rel (Provable_TSP_WC (ChecksDerivation := ChecksDerivation))
        K Machine_TSP (fun x => x) omegaΓ = ∅)
    (pc : PolyCompressionWC_TSP ChecksDerivation omegaΓ) :
    RevHalt.ProofComplexity.PolynomiallyBoundedPPS
      (TSP_PPS ChecksDerivation omegaΓ
        (ChecksWC_complete_of_PolyPosWC_TSP (ChecksDerivation := ChecksDerivation) omegaΓ
          (PolyPosWC_TSP_of_Stable_of_decidable
            (ChecksDerivation := ChecksDerivation)
            K omegaΓ hKMono hDec hEmpty pc)))
      TSPSize :=
  PolyPosWC_TSP_implies_PolyPPS
    (ChecksDerivation := ChecksDerivation)
    omegaΓ
    (PolyPosWC_TSP_of_Stable_of_decidable
      (ChecksDerivation := ChecksDerivation)
      K omegaΓ hKMono hDec hEmpty pc)

end RevHalt.TSP
