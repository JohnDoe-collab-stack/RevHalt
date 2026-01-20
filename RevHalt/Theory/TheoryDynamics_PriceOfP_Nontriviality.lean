import RevHalt.Theory.TheoryDynamics_CanonizationWC
import Mathlib.Data.Nat.Pairing

namespace RevHalt.CanonizationWC

open RevHalt
open RevHalt.ProofCarrying.Witness

/-!
Non-triviality checks for the "Price of P" hypothesis (`PolyCompressionWC`).

This file provides small separation lemmas/examples showing that:
- `PolyCompressionWC` does not imply positive completeness (`PosCompleteWC`).
- `PolyCompressionWC` is not automatic (there are simple systems where it cannot hold).
-/

section Generic

variable {PropT : Type}
variable (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)
variable (ChecksWitness : PropT → List ℕ → Bool)
variable (decodeList : ℕ → List ℕ)

theorem not_PosCompleteWC_of_no_provable
    (IsTrue : PropT → Prop)
    (Γ : Set PropT)
    (hNo : ∀ p : PropT,
      ¬ ProvableWC (PropT := PropT)
          (ChecksDerivation := ChecksDerivation)
          (ChecksWitness := ChecksWitness)
          (decodeList := decodeList)
          Γ p)
    (p0 : PropT)
    (hTrue : IsTrue p0) :
    ¬ PosCompleteWC (PropT := PropT)
        (IsTrue := IsTrue)
        (ChecksDerivation := ChecksDerivation)
        (ChecksWitness := ChecksWitness)
        (decodeList := decodeList)
        Γ := by
  intro pos
  exact hNo p0 (pos.pos p0 hTrue)

def polyCompressionWC_of_no_provable
    (Γ : Set PropT)
    (size : PropT → ℕ)
    (hNo : ∀ p : PropT,
      ¬ ProvableWC (PropT := PropT)
          (ChecksDerivation := ChecksDerivation)
          (ChecksWitness := ChecksWitness)
          (decodeList := decodeList)
          Γ p) :
    PolyCompressionWC (PropT := PropT)
        (ChecksDerivation := ChecksDerivation)
        (ChecksWitness := ChecksWitness)
        (decodeList := decodeList)
        Γ size :=
  { B := fun _ => 0
    compress := by
      intro p hp
      exact False.elim ((hNo p) hp)
    B_poly := by
      refine ⟨0, 0, ?_⟩
      intro n
      simp }

end Generic

section Example_NoPolyCompression

open Nat

def ChecksDerivation_id (_Γ : Set ℕ) (p : ℕ) (c : DerivationCode) : Bool :=
  decide (c = p)

def ChecksWitness_true (_p : ℕ) (_w : List ℕ) : Bool :=
  true

def decodeList_nil (_n : ℕ) : List ℕ :=
  []

def size0 (_p : ℕ) : ℕ :=
  0

theorem provableWC_all_nat (Γ : Set ℕ) (p : ℕ) :
    ProvableWC (PropT := ℕ)
      (ChecksDerivation := ChecksDerivation_id)
      (ChecksWitness := ChecksWitness_true)
      (decodeList := decodeList_nil)
      Γ p := by
  refine ⟨⟨Nat.pair p 0, ?_⟩⟩
  simp [RevHalt.ProofCarrying.Witness.ChecksWC,
        ChecksDerivation_id, ChecksWitness_true,
        RevHalt.ProofCarrying.Witness.proofPart,
        RevHalt.ProofCarrying.Witness.unpair_fst]

theorem no_polyCompressionWC_size0 :
    ¬ Nonempty (PolyCompressionWC (PropT := ℕ)
          (ChecksDerivation := ChecksDerivation_id)
          (ChecksWitness := ChecksWitness_true)
          (decodeList := decodeList_nil)
          (Γ := (Set.univ : Set ℕ))
          size0) := by
  intro h
  rcases h with ⟨pc⟩
  let p0 : ℕ := pc.B 0

  have hp0 :
      ProvableWC (PropT := ℕ)
        (ChecksDerivation := ChecksDerivation_id)
        (ChecksWitness := ChecksWitness_true)
        (decodeList := decodeList_nil)
        (Set.univ : Set ℕ) p0 :=
    provableWC_all_nat (Γ := (Set.univ : Set ℕ)) p0

  rcases pc.compress p0 hp0 with ⟨d, hdlt⟩

  -- Extract the derivation-check part from d.valid in a stable way
  have hAnd :
      (ChecksDerivation_id (Set.univ : Set ℕ) p0 (proofPart d.code) = true) ∧
      (ChecksWitness_true p0 (decodeWitness decodeList_nil d.code) = true) := by
    have hv' :
        (ChecksDerivation_id (Set.univ : Set ℕ) p0 (proofPart d.code) &&
         ChecksWitness_true p0 (decodeWitness decodeList_nil d.code)) = true := by
      simpa [RevHalt.ProofCarrying.Witness.ChecksWC] using d.valid
    rw [Bool.and_eq_true] at hv'
    exact hv'

  have hDeriv :
      ChecksDerivation_id (Set.univ : Set ℕ) p0 (proofPart d.code) = true :=
    hAnd.1

  have hEq : proofPart d.code = p0 := by
    have : decide (proofPart d.code = p0) = true := by
      simpa [ChecksDerivation_id] using hDeriv
    exact of_decide_eq_true this

  have hp0_le : p0 ≤ d.code := by
    have hProofLe : proofPart d.code ≤ d.code := by
      simpa [RevHalt.ProofCarrying.Witness.unpair_fst] using (Nat.unpair_left_le d.code)
    simpa [hEq] using hProofLe

  exact (Nat.not_lt_of_ge hp0_le hdlt)

end Example_NoPolyCompression

end RevHalt.CanonizationWC
