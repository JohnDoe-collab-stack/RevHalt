import RevHalt.Theory.ProofComplexity.Correspondence
import RevHalt.Theory.Instances.ThreeSAT_Canonization

/-!
# 3SAT ↔ Proof Complexity (PPS) Correspondence

Concrete, constructive endpoint (objective A):

`PolyPosWC` for the 3SAT witness-carrying system implies a polynomially bounded PPS
for the induced verifier (based on `ChecksWC`).

No `noncomputable`, no `classical`.
-/

namespace RevHalt.ThreeSATCanonization

open RevHalt.ProofCarrying.Witness
open RevHalt.ThreeSAT

/-- Local alias: `PolyPosWC` specialized to the 3SAT checker. -/
def PolyPosWC_3SAT
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  RevHalt.Complexity.PolyPosWC
    Γ ChecksDerivation ChecksWitness_3SAT decodeList SATSize IsTrue_3SAT

/-- Soundness: if the WC checker accepts, then the instance is true (`IsTrue_3SAT`). -/
theorem IsTrue_3SAT_of_ChecksWC
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ) :
    ∀ p,
      (∃ c, ChecksWC ChecksDerivation ChecksWitness_3SAT decodeList Γ p c) →
      IsTrue_3SAT p := by
  intro p h
  rcases h with ⟨c, hCheck⟩
  have hCheck' : ChecksWC ChecksDerivation ChecksWitness_3SAT decodeList Γ p c = true := by
    simpa using hCheck
  have hValid := hCheck'
  unfold ChecksWC at hValid
  simp only [Bool.and_eq_true] at hValid
  have hWitnessCheck :
      ChecksWitness_3SAT p (decodeWitness decodeList c) = true := hValid.2
  cases hdec : decode3SAT p with
  | none =>
      have : False := by
        simp [ChecksWitness_3SAT, hdec] at hWitnessCheck
      exact False.elim this
  | some inst =>
      have hSat : satWitness inst (decodeWitness decodeList c) = true := by
        simpa [ChecksWitness_3SAT, hdec] using hWitnessCheck
      exact ⟨inst, hdec, ⟨decodeWitness decodeList c, hSat⟩⟩

/-- Completeness of `ChecksWC` derived from `PolyPosWC_3SAT`. -/
theorem ChecksWC_complete_of_PolyPosWC_3SAT
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ)
    (hPoly : PolyPosWC_3SAT ChecksDerivation Γ) :
    ∀ p, IsTrue_3SAT p → ∃ c, ChecksWC ChecksDerivation ChecksWitness_3SAT decodeList Γ p c := by
  intro p hTrue
  rcases hPoly.pos_short p hTrue with ⟨d, _hBound⟩
  exact ⟨d.code, d.valid⟩

/-- The induced PPS for 3SAT, parameterized by an explicit completeness proof. -/
def SAT_PPS
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ)
    (hComplete :
      ∀ p, IsTrue_3SAT p → ∃ c, ChecksWC ChecksDerivation ChecksWitness_3SAT decodeList Γ p c) :
    RevHalt.ProofComplexity.PropositionalProofSystem IsTrue_3SAT WCCode id :=
  RevHalt.ProofComplexity.toPPS
    (Γ := Γ)
    (ChecksDerivation := ChecksDerivation)
    (ChecksWitness := ChecksWitness_3SAT)
    (decodeList := decodeList)
    (HasSolution := IsTrue_3SAT)
    (hSound := IsTrue_3SAT_of_ChecksWC (ChecksDerivation := ChecksDerivation) Γ)
    (hComplete := hComplete)

/-- Main endpoint (objective A, concrete): `PolyPosWC_3SAT` implies poly-bounded PPS. -/
def PolyPosWC_3SAT_implies_PolyPPS
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ)
    (hPoly : PolyPosWC_3SAT ChecksDerivation Γ) :
    RevHalt.ProofComplexity.PolynomiallyBoundedPPS
      (SAT_PPS ChecksDerivation Γ
        (ChecksWC_complete_of_PolyPosWC_3SAT (ChecksDerivation := ChecksDerivation) Γ hPoly))
      SATSize :=
  RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS
    (Γ := Γ)
    (ChecksDerivation := ChecksDerivation)
    (ChecksWitness := ChecksWitness_3SAT)
    (decodeList := decodeList)
    (size := SATSize)
    (HasSolution := IsTrue_3SAT)
    (hSound := IsTrue_3SAT_of_ChecksWC (ChecksDerivation := ChecksDerivation) Γ)
    (hComplete := ChecksWC_complete_of_PolyPosWC_3SAT (ChecksDerivation := ChecksDerivation) Γ hPoly)
    (hPoly := hPoly)

end RevHalt.ThreeSATCanonization
