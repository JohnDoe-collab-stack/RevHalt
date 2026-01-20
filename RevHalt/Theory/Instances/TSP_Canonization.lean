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
  **Completeness from Empty Frontier**:
  If the "Route II" frontier (S1Rel) is empty at the trajectory limit,
  then every true instance is provable (PosCompleteWC).

  This is the core Layer 2 theorem:
  Stability (S1Rel = ∅) → Canonization (PosCompleteWC)
-/
theorem PosCompleteWC_of_S1Rel_empty_TSP_of_decidable
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hDec : DecidablePred (fun p => Provable_TSP_WC (ChecksDerivation:=ChecksDerivation) ωΓ p))
    (hEmpty : S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) K Machine_TSP (fun x => x) ωΓ = ∅) :
    RevHalt.CanonizationWC.PosCompleteWC
      (PropT:=ℕ)
      (IsTrue:=IsTrue_TSP)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness_TSP)
      (decodeList:=decodeList)
      ωΓ := by
  refine { pos := ?_ }
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

  -- 3. Decidable split on provability at ωΓ (no classical)
  haveI : Decidable (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation) ωΓ p) := hDec p
  by_cases hProv : Provable_TSP_WC (ChecksDerivation:=ChecksDerivation) ωΓ p
  · exact hProv
  · -- 4. If not provable, then p ∈ S1Rel, contradicting emptiness
    have hIn : p ∈ S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP (fun x => x) ωΓ := by
      unfold S1Rel
      simp only [Set.mem_setOf_eq]
      unfold Provable_TSP_WC
      exact ⟨p, rfl, hRev0, hProv⟩
    rw [hEmpty] at hIn
    exact False.elim hIn


--
-- Objective A (constructive glue):
-- turn “stability at ωΓ” + “Price of P” into the standard `PolyPosWC_TSP` object,
-- without any classical choice (but requiring an explicit decidability hypothesis).
--

/--
  **Closure of Layer 2 (constructive)**:
  `(S1Rel = ∅ at ωΓ)` + `PolyCompressionWC_TSP` ⇒ `PolyPosWC_TSP`,
  under an explicit decidability hypothesis on WC-provability at `ωΓ`.
-/
def PolyPosWC_TSP_of_Stable_of_decidable
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (ωΓ : Set ℕ)
    (hKMono : RevHalt.DetectsMono K)
    (hDec : DecidablePred (fun p => Provable_TSP_WC (ChecksDerivation:=ChecksDerivation) ωΓ p))
    (hEmpty : S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP (fun x => x) ωΓ = ∅)
    (pc : PolyCompressionWC_TSP ChecksDerivation ωΓ) :
    PolyPosWC_TSP ChecksDerivation ωΓ := by
  let pos :
      RevHalt.CanonizationWC.PosCompleteWC
        (PropT:=ℕ)
        (IsTrue:=IsTrue_TSP)
        (ChecksDerivation:=ChecksDerivation)
        (ChecksWitness:=ChecksWitness_TSP)
        (decodeList:=decodeList)
        ωΓ :=
    PosCompleteWC_of_S1Rel_empty_TSP_of_decidable
      (ChecksDerivation:=ChecksDerivation) K ωΓ hKMono hDec hEmpty
  exact
    RevHalt.CanonizationWC.PolyPosWC_of_PosComplete_and_PolyCompression
      (PropT:=ℕ) (IsTrue:=IsTrue_TSP)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness_TSP)
      (decodeList:=decodeList)
      (Γ:=ωΓ) (size:=TSPSize)
      pos pc

end RevHalt.TSP
