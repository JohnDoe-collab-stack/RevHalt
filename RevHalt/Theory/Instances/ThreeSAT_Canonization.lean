import RevHalt.Theory.TheoryDynamics_CanonizationWC
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds
import RevHalt.Theory.Instances.ThreeSAT

namespace RevHalt.ThreeSATCanonization

open RevHalt
open RevHalt.CanonizationWC
open RevHalt.ProofCarrying.Witness
open RevHalt.ThreeSAT

/-- Ground truth: code decodes to a satisfiable 3SAT instance. -/
def IsTrue_3SAT (p : ℕ) : Prop :=
  ∃ inst, decode3SAT p = some inst ∧ HasSolution inst

/-- Witness checker: witness = assignment bits. -/
def ChecksWitness_3SAT (p : ℕ) (w : List ℕ) : Bool :=
  match decode3SAT p with
  | none => false
  | some inst => satWitness inst w

/-- Provability relation instantiated with WC. -/
def Provable_3SAT_WC
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (Γ : Set ℕ) (p : ℕ) : Prop :=
  ProvableWC (PropT:=ℕ)
    (ChecksDerivation:=ChecksDerivation)
    (ChecksWitness:=ChecksWitness_3SAT)
    (decodeList:=decodeList)
    Γ p

/-- Size measure (computable). You can refine later. -/
def SATSize (p : ℕ) : ℕ := p

/-!
## Price-of-P objects (3SAT)

This file provides the 3SAT analog of the TSP canonization interface:

- `PolyCompressionWC_3SAT` is the concrete “Price of P” hypothesis (WC-compression is polynomial).
- `PolyPosWC_3SAT` is the concrete “poly bounded WC proofs” object.
- `PolyPosWC_3SAT_of_Stable_of_decidable` is the end-to-end bridge:
  stability (`S1Rel = ∅`) + Price-of-P ⇒ `PolyPosWC_3SAT`.
-/

/-- 3SAT: polynomial witness-carrying object (`PolyPosWC`) specialized to this checker. -/
def PolyPosWC_3SAT
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  RevHalt.Complexity.PolyPosWC
    Γ ChecksDerivation ChecksWitness_3SAT decodeList SATSize IsTrue_3SAT

/-- 3SAT: “Price of P” object (`PolyCompressionWC`) specialized to this checker. -/
abbrev PolyCompressionWC_3SAT
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  RevHalt.CanonizationWC.PolyCompressionWC
    (PropT := ℕ)
    (ChecksDerivation := ChecksDerivation)
    (ChecksWitness := ChecksWitness_3SAT)
    (decodeList := decodeList)
    Γ SATSize

/--
Constructive version of "Stability ⇒ PosCompleteWC":
we assume decidability of provability at ωΓ to avoid `classical`.
-/
theorem PosCompleteWC_of_S1Rel_empty_3SAT
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hDec : DecidablePred (fun p => Provable_3SAT_WC (ChecksDerivation:=ChecksDerivation) ωΓ p))
    (hEmpty : S1Rel (Provable_3SAT_WC (ChecksDerivation:=ChecksDerivation))
                    K Machine_3SAT (fun x => x) ωΓ = ∅) :
    RevHalt.CanonizationWC.PosCompleteWC
      (PropT:=ℕ)
      (IsTrue:=IsTrue_3SAT)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness_3SAT)
      (decodeList:=decodeList)
      ωΓ := by
  refine { pos := ?_ }
  intro p hTrue
  rcases hTrue with ⟨inst, hdec, hsol⟩
  have hHalts : Halts (Machine_3SAT p) := (Machine_3SAT_halts_iff (code:=p) (inst:=inst) hdec).2 hsol
  have hRev0 : RevHalt.Rev0_K K (Machine_3SAT p) := by
    apply (RevHalt.T1_traces_of_DetectsMono K hKMono (Machine_3SAT p)).mpr
    exact hHalts
  -- Decidable split (no classical)
  haveI : Decidable (Provable_3SAT_WC (ChecksDerivation:=ChecksDerivation) ωΓ p) := hDec p
  by_cases hp : Provable_3SAT_WC (ChecksDerivation:=ChecksDerivation) ωΓ p
  · exact hp
  · -- if not provable, then p ∈ S1Rel, contradict empty
    have hIn : p ∈ S1Rel (Provable_3SAT_WC (ChecksDerivation:=ChecksDerivation))
                          K Machine_3SAT (fun x => x) ωΓ := by
      unfold S1Rel
      refine ⟨p, rfl, hRev0, hp⟩
    -- contradiction with emptiness
    rw [hEmpty] at hIn
    exact False.elim hIn

/-!
### Closing the loop: Stability + Price-of-P ⇒ PolyPosWC (3SAT)

This is the exact 3SAT analog of the TSP lemma
`PolyPosWC_TSP_of_Stable_of_decidable`.
-/

def PolyPosWC_3SAT_of_Stable_of_decidable
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hDec : DecidablePred (fun p => Provable_3SAT_WC (ChecksDerivation := ChecksDerivation) ωΓ p))
    (hEmpty :
      S1Rel (Provable_3SAT_WC (ChecksDerivation := ChecksDerivation))
        K Machine_3SAT (fun x => x) ωΓ = ∅)
    (pc : PolyCompressionWC_3SAT (ChecksDerivation := ChecksDerivation) ωΓ) :
    PolyPosWC_3SAT (ChecksDerivation := ChecksDerivation) ωΓ := by
  -- Stability ⇒ PosCompleteWC (constructive via decidability)
  have pos :
      RevHalt.CanonizationWC.PosCompleteWC
        (PropT := ℕ)
        (IsTrue := IsTrue_3SAT)
        (ChecksDerivation := ChecksDerivation)
        (ChecksWitness := ChecksWitness_3SAT)
        (decodeList := decodeList)
        ωΓ :=
    PosCompleteWC_of_S1Rel_empty_3SAT
      (ChecksDerivation := ChecksDerivation)
      (K := K) (ωΓ := ωΓ) (hKMono := hKMono) (hDec := hDec) (hEmpty := hEmpty)
  -- PosCompleteWC + PolyCompressionWC ⇒ PolyPosWC (generic closure lemma)
  exact
    RevHalt.CanonizationWC.PolyPosWC_of_PosComplete_and_PolyCompression
      (PropT := ℕ)
      (IsTrue := IsTrue_3SAT)
      (ChecksDerivation := ChecksDerivation)
      (ChecksWitness := ChecksWitness_3SAT)
      (decodeList := decodeList)
      (Γ := ωΓ)
      (size := SATSize)
      pos pc

end RevHalt.ThreeSATCanonization
