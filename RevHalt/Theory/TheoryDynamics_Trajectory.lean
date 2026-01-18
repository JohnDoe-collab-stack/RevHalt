import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import Mathlib.Data.Set.Basic
import RevHalt.Theory.Categorical

namespace RevHalt

open Set
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRAJECTORY DYNAMICS: The Effective Object
-- ═══════════════════════════════════════════════════════════════════════════════

section TrajectoryDynamics

universe u

variable {PropT : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable {Code : Type u}
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/-- A trajectory is an infinite sequence of theory states. -/
abbrev Trajectory := ℕ → Set PropT

/-- A trajectory is F0-compatible if each step is F0-generated. -/
def IsF0Trajectory (traj : Trajectory (PropT := PropT)) (Γ0 : Set PropT) : Prop :=
  traj 0 = Γ0 ∧ ∀ n, traj (n + 1) = F0 Provable K Machine encode_halt (traj n)

/-- The canonical trajectory starting from Γ0. -/
def canonicalTrajectory (Γ0 : Set PropT) : Trajectory (PropT := PropT) :=
  chain0 Provable K Machine encode_halt Γ0

/-- The canonical trajectory is F0-compatible. -/
theorem canonicalTrajectory_is_F0 (Γ0 : Set PropT) :
    IsF0Trajectory Provable K Machine encode_halt
      (canonicalTrajectory Provable K Machine encode_halt Γ0) Γ0 := by
  constructor
  · rfl
  · intro n; rfl

/--
**Trajectory Uniqueness**: Any F0-compatible trajectory equals the canonical one.
-/
theorem trajectory_unique (Γ0 : Set PropT) (traj : Trajectory (PropT := PropT))
    (hTraj : IsF0Trajectory Provable K Machine encode_halt traj Γ0) :
    traj = canonicalTrajectory Provable K Machine encode_halt Γ0 := by
  funext n
  induction n with
  | zero => exact hTraj.1
  | succ n ih =>
      have h1 : traj (n + 1) = F0 Provable K Machine encode_halt (traj n) := hTraj.2 n
      have h2 : canonicalTrajectory Provable K Machine encode_halt Γ0 (n + 1) =
                F0 Provable K Machine encode_halt (canonicalTrajectory Provable K Machine encode_halt Γ0 n) := rfl
      rw [h1, h2, ih]

/--
**Initial-Dependence**: Different initial states yield different trajectories,
since the trajectory is fully determined by its value at time 0.
-/
theorem trajectory_initial_dependence
    {Γ0 Δ0 : Set PropT}
    (hNe : Γ0 ≠ Δ0) :
    canonicalTrajectory Provable K Machine encode_halt Γ0 ≠
    canonicalTrajectory Provable K Machine encode_halt Δ0 := by
  intro hContra
  have h0 : canonicalTrajectory Provable K Machine encode_halt Γ0 0 =
            canonicalTrajectory Provable K Machine encode_halt Δ0 0 := by
    rw [hContra]
  simp only [canonicalTrajectory, chain0] at h0
  exact hNe h0

/--
**Strict Growth Along Trajectory**: If witness exists at each stage,
the trajectory is strictly increasing.
-/
theorem trajectory_strict_growth
    (Γ0 : Set PropT)
    (hAbs : ∀ n, Absorbable Provable (canonicalTrajectory Provable K Machine encode_halt Γ0 n))
    (hW : ∀ n, FrontierWitness Provable K Machine encode_halt
                (canonicalTrajectory Provable K Machine encode_halt Γ0 n)) :
    ∀ n, canonicalTrajectory Provable K Machine encode_halt Γ0 n ⊂
         canonicalTrajectory Provable K Machine encode_halt Γ0 (n + 1) := by
  intro n
  obtain ⟨e, hKit, hNprov⟩ := hW n
  exact strict_step_of_witness_absorbable Provable K Machine encode_halt
    (canonicalTrajectory Provable K Machine encode_halt Γ0 n)
    (hAbs n) e hKit hNprov

/--
**The ω-limit is the trajectory's effective object**.
-/
def trajectoryLimit (Γ0 : Set PropT) : Set PropT :=
  omega0 Provable K Machine encode_halt Γ0

/-- Each stage embeds into the limit. -/
theorem trajectory_stage_le_limit (Γ0 : Set PropT) (n : ℕ) :
    canonicalTrajectory Provable K Machine encode_halt Γ0 n ⊆
    trajectoryLimit Provable K Machine encode_halt Γ0 := by
  exact chain0_le_omega0 Provable K Machine encode_halt Γ0 n

-- ═══════════════════════════════════════════════════════════════════════════════
-- INCARNATION TRILEMMA
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Incarnation Trilemma

The core insight: three properties cannot hold simultaneously for any trajectory.

1. **FrontierRegeneration**: At each step, new certified truths appear that are not yet provable
2. **Admissible Limit**: The ω-limit is a well-formed theory state (Cn-closed, ProvClosed)
3. **Absorption**: What is certified eventually becomes provable

This is NOT Gödel. This is a limit pathology:
> "The system cannot traverse ω without losing one of its structural properties"
-/

/--
**FrontierRegeneration**: At every admissible state, a new frontier witness exists.

This captures: "the external world keeps producing certified truths faster than absorption."

**Derivation from Route II**: This property follows from `frontier_nonempty_of_route_II`
under the conditions:
- `Soundness`: provability in Γ implies provability in the external system
- `NegativeComplete`: non-halting is provable externally
- `Barrier`: T2 barrier (not all sentences decidable)
-/
def FrontierRegeneration' : Prop :=
  ∀ Γ : Set PropT, PostSplitter Provable Γ →
    FrontierWitness Provable K Machine encode_halt Γ

/--
**Derivation of FrontierRegeneration from Route II**.

This theorem formalizes the link: if Route II hypotheses hold uniformly for any state,
then `FrontierRegeneration'` is true.
-/
theorem FrontierRegeneration_of_RouteII_uniform
    {SProvable : PropT → Prop} {SNot : PropT → PropT}
    (hSound : ∀ Γ, Soundness Provable SProvable Γ)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable SNot)
    (hBar   : (∀ e, SProvable (encode_halt e) ∨ SProvable (SNot (encode_halt e))) → False) :
    FrontierRegeneration' Provable K Machine encode_halt := by
  intro Γ _hPS
  have : (S1Rel Provable K Machine encode_halt Γ).Nonempty :=
    frontier_nonempty_of_route_II Provable K Machine encode_halt SProvable SNot
      (hSound Γ) hNeg hBar
  exact FrontierWitness_of_S1Rel_nonempty Provable K Machine encode_halt this

/--
**The Incarnation Principle**: FrontierRegeneration + PostSplitter trajectory implies strict growth.

If regeneration holds, the trajectory is strictly increasing forever.
Note: Absorbable is derived from PostSplitter via `PostSplitter.imp_Absorbable`.
-/
theorem incarnation_strict_growth
    (hRegen : FrontierRegeneration' Provable K Machine encode_halt)
    (Γ0 : Set PropT)
    (hPS : ∀ n, PostSplitter Provable (canonicalTrajectory Provable K Machine encode_halt Γ0 n)) :
    ∀ n, canonicalTrajectory Provable K Machine encode_halt Γ0 n ⊂
         canonicalTrajectory Provable K Machine encode_halt Γ0 (n + 1) := by
  intro n
  -- Derive Absorbable from PostSplitter
  have hAbs : Absorbable Provable (canonicalTrajectory Provable K Machine encode_halt Γ0 n) :=
    PostSplitter.imp_Absorbable Provable (hPS n)
  -- witness at rank n from regeneration
  obtain ⟨e, hKit, hNprov⟩ := hRegen _ (hPS n)
  exact strict_step_of_witness_absorbable Provable K Machine encode_halt
    (canonicalTrajectory Provable K Machine encode_halt Γ0 n)
    hAbs e hKit hNprov

/--
**Incarnation Trilemma (Parametric Form)**:

For any trajectory, the three conditions cannot all hold:
1. Absorbable at step 1
2. OmegaAdmissible at ω-limit
3. RouteIIAt (frontier non-empty) at ω-limit

This is a wrapper around `omega_trilemma_not_all` with full parameters.
-/
theorem incarnation_trilemma
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ¬ (Absorbable Provable
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
       ∧ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
       ∧ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) :=
  omega_trilemma_not_all Provable K Machine encode_halt Cn hMono hCnExt hIdem hProvCn A0

/--
**Crystallized Thesis**: Incarnation = non-passage to limit.

The effective object is the trajectory, because no limit can be both:
- Admissible (well-formed theory state)
- Regenerative (frontier non-empty, Route II holds)

Formally: `incarnation_trilemma` above, or equivalently `omega_trilemma_not_all`.
-/
theorem incarnation_means_no_stable_limit'
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hAbs : Absorbable Provable
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ)
    (hAdm : OmegaAdmissible Provable Cn
              (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) :
    ¬ RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  intro hR
  exact incarnation_trilemma Provable K Machine encode_halt Cn
    hMono hCnExt hIdem hProvCn A0 ⟨hAbs, hAdm, hR⟩




-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL PARAMETRIC THEOREM
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Forced Non-Admissibility**:
  If Absorbable propagates to stage 1 and Route II applies at the limit,
  then the limit CANNOT be admissible.

  (Contrapositive of the trilemma).
-/
theorem forced_not_OmegaAdmissible
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hAbs1 : Absorbable Provable (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ)
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
                    (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) :
    ¬ OmegaAdmissible Provable Cn (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  intro hAdm
  have hRω : RouteIIAt Provable K Machine encode_halt (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) :=
    hRoute hAdm
  exact omega_trilemma_not_all Provable K Machine encode_halt Cn hMono hCnExt hIdem hProvCn A0 ⟨hAbs1, hAdm, hRω⟩

/--
  **The Structural Escape**:
  If:
  1. Absorbable propagates (Stability),
  2. Route II applies to admissible states (Impossibility),
  3. The limit operator is ω-continuous (Categorical coherence),
  4. Provability is preserved by directed unions,

  THEN: Contradiction.

  The interpretation is that **Condition 3 (Continuity)** is the only free variable
  that can break to avoid the contradiction (assuming Route II and Stability are solid).
-/
theorem only_escape_via_continuity
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    -- Hyp 1: Structural stability
    (hAbs1 : Absorbable Provable (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ)
    -- Hyp 2: Route II linkage
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
                    (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0))
    -- Hyp 3 & 4: Admissibility from Continuity
    (hω : CnOmegaContinuous Cn)
    (hPCdir : ProvClosedDirected Provable) :
    False := by
  -- Construct Admissibility from Continuity assumptions
  have hAdm : OmegaAdmissible Provable Cn (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) :=
    omegaΓ_OmegaAdmissible Provable K Machine encode_halt Cn hCnExt hIdem hProvCn hPCdir hω A0

  -- Apply forced_not_OmegaAdmissible
  have hNotAdm := forced_not_OmegaAdmissible Provable K Machine encode_halt Cn
                    hMono hCnExt hIdem hProvCn A0 hAbs1 hRoute
  exact hNotAdm hAdm


/-- Lemma: The chainState sequence corresponds exactly to the F-iteration. -/
lemma chainState_eq_iter
    (Cn : Set PropT → Set PropT)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ∀ n, (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ =
         iter (F Provable K Machine encode_halt Cn) A0.Γ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [chainState, iter, FState, F, ih]

/--
  **The Canonical Structural Theorem**:
  (1) Stability + (2) Route II ⇒ (3) Rupture of Continuity.

  This is the final "publication form" of the result:
  Given structural stability (Absorbable) and structural impossibility (Route II),
  the dynamic step function `F` **cannot** be ω-continuous.
-/
theorem structural_escape_explicit
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCdir : ProvClosedDirected Provable)
    (A0 : ThState (PropT := PropT) Provable Cn)
    -- Hyp 1: Structural stability
    (hAbs1 : Absorbable Provable (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ)
    -- Hyp 2: Route II linkage at limit
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
                    (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) :
    -- Conclusion: The step function is NOT ω-continuous
    ¬ OmegaContinuousSet (F Provable K Machine encode_halt Cn) := by
  intro hω
  let F_dyn := F Provable K Machine encode_halt Cn

  -- 1. Identify limit as omegaUnion
  have h_lim : (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) =
               omegaUnion (iter F_dyn A0.Γ) := by
    dsimp [omegaΓ, omegaUnion]
    dsimp [F_dyn]
    simp_rw [chainState_eq_iter Provable K Machine encode_halt Cn hIdem hProvCn A0]

  -- 2. Continuity implies Fixpoint
  have hFix : F_dyn (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) =
              (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
    rw [h_lim]
    apply omega_fixpoint_of_OmegaContinuousSet
    · exact hω
    · intro n
      rw [<-chainState_eq_iter Provable K Machine encode_halt Cn hIdem hProvCn A0 n]
      rw [<-chainState_eq_iter Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)]
      exact chainState_mono Provable K Machine encode_halt Cn hCnExt hIdem hProvCn A0 n (n + 1) (Nat.le_succ n)

  -- 3. Fixpoint implies Admissibility (Robust Algebraic Proof)
  let ωΓ := omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0
  let Sω := S1Rel Provable K Machine encode_halt ωΓ

  have hFix_symm : ωΓ = Cn (ωΓ ∪ Sω) := by
    symm; simpa [F_dyn, F, Sω] using hFix

  have hCnClosed : Cn ωΓ = ωΓ := by
    -- Step 1: Cn ω = Cn (Cn ...)
    have hStep1 : Cn ωΓ = Cn (Cn (ωΓ ∪ Sω)) :=
      congrArg Cn hFix_symm
    -- Step 2: Cn (Cn ...) = Cn (...)
    have hStep2 : Cn (Cn (ωΓ ∪ Sω)) = Cn (ωΓ ∪ Sω) :=
      hIdem (ωΓ ∪ Sω)
    -- Step 3: Cn (...) = ω
    have hStep3 : Cn (ωΓ ∪ Sω) = ωΓ :=
      hFix_symm.symm
    -- Combine
    rw [hStep1, hStep2, hStep3]

  have hAdm : OmegaAdmissible Provable Cn ωΓ := by
    constructor
    · exact hCnClosed
    · apply omegaΓ_provClosed_of_directed Provable K Machine encode_halt Cn hCnExt hIdem hProvCn hPCdir A0

  -- 4. Apply Trilemma via forced theorem
  exact forced_not_OmegaAdmissible Provable K Machine encode_halt Cn
    hMono hCnExt hIdem hProvCn A0 hAbs1 hRoute hAdm


end TrajectoryDynamics

end RevHalt
