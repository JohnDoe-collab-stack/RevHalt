import RevHalt.Theory.TheoryDynamics_Trajectory
import RevHalt.Theory.Instances.TSP
import RevHalt.Theory.Instances.TSP_Canonization

namespace RevHalt.TSP

open RevHalt
open RevHalt.ProofCarrying.Witness
open RevHalt.CanonizationWC

-- Identity encoding for TSP instances in Layer 3 (Nat -> Nat)
abbrev Enc : ℕ → ℕ := id

/--
  **Provable_TSP_WC_monotone**:
  Monotonicity of the TSP witness-carrying provability predicate.
  Derived from the monotonicity of the derivation checker.
-/
theorem Provable_TSP_WC_monotone
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (hDerMono : ChecksDerivationMonotone ChecksDerivation) :
    ProvRelMonotone (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) := by
  unfold Provable_TSP_WC
  exact ProvableWC_monotone ChecksDerivation ChecksWitness_TSP decodeList hDerMono


/--
  **Layer 3: S1Rel Empty at Omega**:
  Produces the stability result (S1Rel = ∅) at the trajectory limit ωΓ.

  Hypotheses:
  1. Chain properties (Extensive, Idempotent, ProvClosed).
  2. Trajectory Choice: Absorbable (Start) + OmegaAdmissible (Limit).

  Logic:
  (Absorbable ∧ OmegaAdmissible) ⇒ ¬RouteIIAt (via Trilemma)
  ¬RouteIIAt ⇒ S1Rel = ∅
-/
theorem S1Rel_empty_at_omega_of_absorbable_and_admissible
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (Cn : Set ℕ → Set ℕ)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) Cn)
    (hMono : ProvRelMonotone (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)))
    (A0 : ThState (PropT:=ℕ) (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) Cn)
    (hAbs : Absorbable (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              (chainState (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
                K Machine_TSP Enc Cn hIdem hProvCn A0 1).Γ)
    (hAdm : OmegaAdmissible (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              Cn
              (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
                K Machine_TSP Enc Cn hIdem hProvCn A0)) :
    S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
      K Machine_TSP Enc
      (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP Enc Cn hIdem hProvCn A0) = ∅ := by

  -- 1) Trilemma: (Abs ∧ Adm ∧ RouteII) is impossible
  have hTri :
    ¬ (Absorbable (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
          (chainState (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
            K Machine_TSP Enc Cn hIdem hProvCn A0 1).Γ
       ∧ OmegaAdmissible (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
            Cn
            (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              K Machine_TSP Enc Cn hIdem hProvCn A0)
       ∧ RouteIIAt (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
            K Machine_TSP Enc
            (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              K Machine_TSP Enc Cn hIdem hProvCn A0)) :=
    incarnation_trilemma
      (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
      K Machine_TSP Enc Cn
      hMono hCnExt hIdem hProvCn A0

  -- 2) Abs + Adm implies ¬RouteIIAt
  have hNotRoute :
    ¬ RouteIIAt (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP Enc
        (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
          K Machine_TSP Enc Cn hIdem hProvCn A0) := by
    intro hRoute
    exact hTri ⟨hAbs, hAdm, hRoute⟩

  -- 3) ¬RouteIIAt ⇒ S1Rel = ∅ (Logic: Nonempty S1Rel ⇒ RouteIIAt)
  by_contra hNe
  have hNonempty :
    (S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
      K Machine_TSP Enc
      (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
        K Machine_TSP Enc Cn hIdem hProvCn A0)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hNe
  exact hNotRoute hNonempty


/--
  **Collapse_TSP_of_TrajectoryChoice_and_PriceOfP**:
  The Final End-to-End API.

  Inputs:
  1. Trajectory Choices: Absorbable (Start) + OmegaAdmissible (Limit).
  2. Trajectory Mechanism: K (Monotonic), Cn (Canonizer).
  3. Complexity Hypothesis: Price of P (PolyCompressionWC).

  Output:
  Collapse (P = NP for TSP).
-/
def Collapse_TSP_of_TrajectoryChoice_and_PriceOfP
    {ChecksDerivation : Set ℕ → ℕ → DerivationCode → Bool}
    (K : RHKit)
    (Cn : Set ℕ → Set ℕ)
    (hKMono : DetectsMono K)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) Cn)
    (hMono : ProvRelMonotone (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)))
    (A0 : ThState (PropT:=ℕ) (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation)) Cn)
    (hAbs : Absorbable (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              (chainState (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
                K Machine_TSP Enc Cn hIdem hProvCn A0 1).Γ)
    (hAdm : OmegaAdmissible (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              Cn
              (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
                K Machine_TSP Enc Cn hIdem hProvCn A0))
    (pc : PolyCompressionWC_TSP ChecksDerivation
            (omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
              K Machine_TSP Enc Cn hIdem hProvCn A0)) :
    Collapse_TSP_Axiom := by

  let ωΓ :=
    omegaΓ (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
      K Machine_TSP Enc Cn hIdem hProvCn A0

  -- 1. Derive Stability (Layer 3)
  have hEmpty :
    S1Rel (Provable_TSP_WC (ChecksDerivation:=ChecksDerivation))
      K Machine_TSP Enc ωΓ = ∅ :=
    S1Rel_empty_at_omega_of_absorbable_and_admissible
      (ChecksDerivation:=ChecksDerivation)
      K Cn hCnExt hIdem hProvCn hMono A0 hAbs hAdm

  -- 2. Call Layer 2 API (Stability + PriceOfP => Collapse)
  exact Collapse_TSP_of_Stable_and_PriceOfP
    (ChecksDerivation:=ChecksDerivation)
    K ωΓ hKMono hEmpty pc

end RevHalt.TSP
