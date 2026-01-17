import RevHalt.Theory.TheoryDynamics_CanonizationWC
import RevHalt.Theory.TheoryDynamics_ComplexityBounds
import RevHalt.Theory.Instances.TSP

namespace RevHalt.TSP

open RevHalt.CanonizationWC


open RevHalt.ProofCarrying.Witness

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
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
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
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  BoundPosWC (PropT:=ℕ) IsTrue_TSP ChecksDerivation ChecksWitness_TSP decodeList Γ TSPSize

/--
  **PolyPosWC for TSP**: The stronger "Price of P" object.
  This is just a BoundPosWC where the bound is polynomial.
-/
def PolyPosWC_TSP
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
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
    -- We use the property that K detects halting for any trace if K is monotonic.
    -- (T1_traces_of_DetectsMono is the bridge).
    have hRev0 : RevHalt.Rev0_K K (Machine_TSP p) := by
      apply (RevHalt.T1_traces_of_DetectsMono K hKMono (Machine_TSP p)).mpr
      exact hHalts

    -- 3. If NOT Provable, then p ∈ S1Rel
    -- 3. If NOT Provable, then p ∈ S1Rel
    classical
    by_contra hNProv
    have hIn : p ∈ S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) K Machine_TSP (fun x => x) ωΓ := by
      unfold S1Rel
      simp only [Set.mem_setOf_eq]
      unfold Provable_TSP_WC
      refine ⟨p, rfl, hRev0, hNProv⟩

    -- 4. Contradiction with empty S1Rel
    -- 4. Contradiction with empty S1Rel
    simpa [hEmpty] using hIn
}


/--
  **PolyCompressionWC_TSP**:
  The "Price of P" hypothesis for TSP:
  "If a TSP instance is WC-provable, there exists a polynomial-size derivation."
-/
abbrev PolyCompressionWC_TSP
    (ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool)
    (Γ : Set ℕ) : Type :=
  RevHalt.CanonizationWC.PolyCompressionWC
    (PropT:=ℕ)
    (ChecksDerivation:=ChecksDerivation)
    (ChecksWitness:=ChecksWitness_TSP)
    (decodeList:=decodeList)
    Γ TSPSize

/--
  **Closure of Layer 2**:
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
  -- 1. Layer 2 Result: PosCompleteWC
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
  **End-to-End**: Stability + Price of P ⇒ Collapse.
  This is the single function that projects Layer 2 stability into Layer 1 collapse.
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
