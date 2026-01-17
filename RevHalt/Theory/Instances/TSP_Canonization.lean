import RevHalt.Theory.TheoryDynamics_CanonizationWC
import RevHalt.Theory.Instances.TSP

namespace RevHalt.TSP

open RevHalt.CanonizationWC

/-
  **TSP Canonization Layer**
  Instantiates the generic Layer 2 infrastructure for the Traveling Salesman Problem.
-/

/--
  **IsTrue_TSP**: Ground truth definition.
  A code `p` is true if it decodes to a valid TSP instance that has a solution.
-/
def IsTrue_TSP (p : ℕ) : Prop :=
  ∃ inst, decodeTSP p = some inst ∧ HasSolution inst

/--
  **Provable_TSP_WC**: Witness-carrying provability for TSP.
  Uses the standard TSP checkers and decoders.
-/
def Provable_TSP_WC
    {ChecksDerivation : Set ℕ → ℕ → RevHalt.ProofCarrying.Witness.DerivationCode → Bool}
    (Γ : Set ℕ) (p : ℕ) : Prop :=
  ProvableWC (PropT:=ℕ)
    (ChecksDerivation:=ChecksDerivation)
    (ChecksWitness:=ChecksWitness_TSP)
    (decodeList:=decodeList)
    Γ p

/--
  **BoundPosWC for TSP**: The constructive object asserting existence of short derivations.
  This is the Layer 2 output we want to produce.
-/
def BoundPosWC_TSP
    (ChecksDerivation : Set ℕ → ℕ → RevHalt.ProofCarrying.Witness.DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  BoundPosWC (PropT:=ℕ) IsTrue_TSP ChecksDerivation ChecksWitness_TSP decodeList Γ TSPSize

/--
  **PolyPosWC for TSP**: The stronger "Price of P" object.
  This is just a BoundPosWC where the bound is polynomial.
-/
def PolyPosWC_TSP
    (ChecksDerivation : Set ℕ → ℕ → RevHalt.ProofCarrying.Witness.DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  RevHalt.Complexity.PolyPosWC Γ ChecksDerivation ChecksWitness_TSP decodeList TSPSize IsTrue_TSP

/--
  **Completeness from Empty Frontier**:
  If the "Route II" frontier (S1Rel) is empty at the trajectory limit,
  then every true instance is provable (PosCompleteWC).

  This is the core Layer 2 theorem:
  Stability (S1Rel = ∅) → Canonization (PosCompleteWC)
-/
theorem PosCompleteWC_of_S1Rel_empty_TSP
    {ChecksDerivation : Set ℕ → ℕ → RevHalt.ProofCarrying.Witness.DerivationCode → Bool}
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
    -- We use the property that K detects halting for any trace if K is monotonic.
    -- (T1_traces_of_DetectsMono is the bridge).
    have hRev0 : RevHalt.Rev0_K K (Machine_TSP p) := by
      apply (RevHalt.T1_traces_of_DetectsMono K hKMono (Machine_TSP p)).mpr
      exact hHalts

    -- 3. If NOT Provable, then p ∈ S1Rel
    by_contra hNProv
    have hIn : p ∈ S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) K Machine_TSP (fun x => x) ωΓ := by
      unfold S1Rel
      simp only [Set.mem_setOf_eq]
      -- S1Rel = {x | Rev0_K(M(x)) ∧ ¬Provable(f(x))}
      refine ⟨p, rfl, hRev0, hNProv⟩

    -- 4. Contradiction with empty S1Rel
    rw [hEmpty] at hIn
    exact hIn
}

end RevHalt.TSP
