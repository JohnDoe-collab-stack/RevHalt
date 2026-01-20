import RevHalt.Theory.Instances.TSP_Canonization

namespace RevHalt.TSP

open RevHalt
open RevHalt.CanonizationWC
open RevHalt.ProofCarrying.Witness

/-!
# TSP Canonization (classical glue)

This file isolates the non-constructive step:

`S1Rel = ∅  ->  PosCompleteWC`

without an explicit decidability hypothesis on WC-provability.

Everything here is intentionally classical; keep constructive endpoints in
`RevHalt/Theory/Instances/TSP_Canonization.lean` and
`RevHalt/Theory/Instances/TSP_ProofComplexity.lean`.
-/

/--
  **Completeness from Empty Frontier (classical)**:
  if `S1Rel = ∅` at the limit, then every true instance is provable (PosCompleteWC).

  This uses `by_contra` to eliminate double negation without a decidability hypothesis.
-/
theorem PosCompleteWC_of_S1Rel_empty_TSP
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hEmpty : S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) K Machine_TSP (fun x => x) ωΓ = ∅) :
    RevHalt.CanonizationWC.PosCompleteWC
      (PropT:=ℕ)
      (IsTrue:=IsTrue_TSP)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness_TSP)
      (decodeList:=decodeList)
      ωΓ := {
  pos := by
    intro p hTrue
    -- 1. IsTrue_TSP p implies Machine_TSP p halts
    obtain ⟨inst, hDecode, hSol⟩ := hTrue
    have hHalts : RevHalt.Halts (Machine_TSP p) := by
      rw [RevHalt.TSP.Machine_TSP_halts_iff hDecode]
      exact hSol

    -- 2. Halts implies K-detection (via DetectsMono)
    have hRev0 : RevHalt.Rev0_K K (Machine_TSP p) := by
      apply (RevHalt.T1_traces_of_DetectsMono K hKMono (Machine_TSP p)).mpr
      exact hHalts

    -- 3. If NOT provable, then p ∈ S1Rel
    classical
    by_contra hNProv
    have hIn : p ∈ S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP (fun x => x) ωΓ := by
      unfold S1Rel
      simp only [Set.mem_setOf_eq]
      unfold Provable_TSP_WC
      refine ⟨p, rfl, hRev0, hNProv⟩

    -- 4. Contradiction with empty S1Rel
    rw [hEmpty] at hIn
    exact hIn.elim
}

/--
  **Closure of Layer 2 (classical)**:
  (Stability ⇒ PosCompleteWC) + (Price of P ⇒ PolyCompressionWC) ⇒ PolyPosWC
-/
def PolyPosWC_TSP_of_Stable
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit) (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hEmpty : S1Rel
        (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP (fun x => x) ωΓ = ∅)
    (pc : PolyCompressionWC_TSP ChecksDerivation ωΓ) :
    PolyPosWC_TSP ChecksDerivation ωΓ := by
  -- 1. Layer 2 Result: PosCompleteWC (classical step)
  let pos : PosCompleteWC
      (PropT:=ℕ) (IsTrue:=IsTrue_TSP)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness_TSP)
      (decodeList:=decodeList)
      ωΓ :=
    PosCompleteWC_of_S1Rel_empty_TSP
      (ChecksDerivation:=ChecksDerivation) K ωΓ hKMono hEmpty
  -- 2. Closure via Price of P
  exact RevHalt.CanonizationWC.PolyPosWC_of_PosComplete_and_PolyCompression
    (PropT:=ℕ) (IsTrue:=IsTrue_TSP)
    (ChecksDerivation:=ChecksDerivation)
    (ChecksWitness:=ChecksWitness_TSP)
    (decodeList:=decodeList)
    (Γ:=ωΓ) (size:=TSPSize)
    pos pc

/--
  **End-to-End (classical)**: Stability + Price of P ⇒ Collapse.
  This projects Layer 2 stability into Layer 1 collapse.
-/
def Collapse_TSP_of_Stable_and_PriceOfP
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit) (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hEmpty : S1Rel
        (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP (fun x => x) ωΓ = ∅)
    (pc : PolyCompressionWC_TSP ChecksDerivation ωΓ) :
    Collapse_TSP_Axiom := by
  let poly := PolyPosWC_TSP_of_Stable (ChecksDerivation:=ChecksDerivation) K ωΓ hKMono hEmpty pc
  exact Collapse_of_Trajectory_Poly (ωΓ:=ωΓ) poly

end RevHalt.TSP

