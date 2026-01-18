import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_Trajectory

namespace RevHalt.Trilemma

universe u

variable {PropT : Type u}
variable {Code : Type u}

section ChainState

variable (Provable : Set PropT -> PropT -> Prop)
variable (K : RHKit)
variable (Machine : Code -> Trace)
variable (encode_halt : Code -> PropT)
variable (Cn : Set PropT -> Set PropT)
variable (A0 : ThState (PropT := PropT) Provable Cn)

/-- Spiral step: strict extension from a frontier witness. -/
theorem spiral_step_strict
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat)
    (hPS : PostSplitter Provable
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ)
    (hW : FrontierWitness Provable K Machine encode_halt
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ
      ⊂
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ := by
  simpa using
    (strict_chainState_step
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn)
      (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (A0 := A0) (n := n) (hPS := hPS) (hW := hW))

/-- Spiral step: monotone extension for every `n`. -/
theorem spiral_step_mono
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ
      ⊆
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ := by
  simpa using
    (chainState_step_hom_def
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn)
      (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (A0 := A0) (n := n))

/-- Bridge: if `Cn` is the identity, chainState matches canonicalTrajectory. -/
theorem chainState_eq_canonicalTrajectory_of_Cn_id
    (hCnId : ∀ Γ : Set PropT, Cn Γ = Γ)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ∀ n,
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ =
      RevHalt.canonicalTrajectory Provable K Machine encode_halt A0.Γ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [chainState_succ, FState, F, hCnId, ih,
        RevHalt.canonicalTrajectory, RevHalt.chain0, RevHalt.F0]

end ChainState

section Trajectory

variable (Provable : Set PropT -> PropT -> Prop)
variable (K : RHKit)
variable (Machine : Code -> Trace)
variable (encode_halt : Code -> PropT)

/-- A trajectory is a spiral if it strictly grows at every step. -/
def IsSpiral (Γ : Nat -> Set PropT) : Prop :=
  ∀ n, Γ n ⊂ Γ (n + 1)

/-- Hypothesis: one-step preservation of PostSplitter along F0. -/
def F0_preserves_PostSplitter : Prop :=
  ∀ Γ : Set PropT,
    PostSplitter Provable Γ →
    PostSplitter Provable (F0 Provable K Machine encode_halt Γ)

/-- PostSplitter propagates along the canonical trajectory if F0 preserves it. -/
theorem PostSplitter_canonicalTrajectory
    (hPSstep : F0_preserves_PostSplitter Provable K Machine encode_halt)
    (Γ0 : Set PropT)
    (hPS0 : PostSplitter Provable Γ0) :
    ∀ n, PostSplitter Provable
      (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n) := by
  intro n
  induction n with
  | zero =>
      simpa [RevHalt.canonicalTrajectory, RevHalt.chain0] using hPS0
  | succ n ih =>
      have hPSn :
          PostSplitter Provable
            (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n) := ih
      simpa [RevHalt.canonicalTrajectory, RevHalt.chain0] using
        (hPSstep _ hPSn)

/-- Trajectory bridge: strict growth of the canonical trajectory. -/
theorem spiral_trajectory_strict_growth
    (hRegen : RevHalt.FrontierRegeneration' Provable K Machine encode_halt)
    (Γ0 : Set PropT)
    (hPS : ∀ n, RevHalt.PostSplitter Provable
      (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n)) :
    ∀ n, RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n ⊂
         RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 (n + 1) := by
  simpa using
    (RevHalt.incarnation_strict_growth
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (hRegen := hRegen)
      (Γ0 := Γ0) (hPS := hPS))

/-- Canonical trajectory is a spiral under regeneration + PostSplitter. -/
theorem canonicalTrajectory_isSpiral
    (hRegen : RevHalt.FrontierRegeneration' Provable K Machine encode_halt)
    (Γ0 : Set PropT)
    (hPS : ∀ n, RevHalt.PostSplitter Provable
      (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n)) :
    IsSpiral (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0) := by
  simpa [IsSpiral] using
    (spiral_trajectory_strict_growth
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      hRegen Γ0 hPS)

/-- Canonical trajectory is a spiral from Route II + PostSplitter propagation. -/
theorem canonicalTrajectory_isSpiral_of_RouteII
    {SProvable : PropT -> Prop} {SNot : PropT -> PropT}
    (hSound : ∀ Γ, Soundness Provable SProvable Γ)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable SNot)
    (hBar   : (∀ e, SProvable (encode_halt e) ∨ SProvable (SNot (encode_halt e))) → False)
    (hPSstep : F0_preserves_PostSplitter Provable K Machine encode_halt)
    (Γ0 : Set PropT)
    (hPS0 : PostSplitter Provable Γ0) :
    IsSpiral (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0) := by
  have hRegen :
      RevHalt.FrontierRegeneration' Provable K Machine encode_halt :=
    RevHalt.FrontierRegeneration_of_RouteII_uniform
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (hSound := hSound)
      (hNeg := hNeg) (hBar := hBar)
  have hPS : ∀ n, RevHalt.PostSplitter Provable
      (RevHalt.canonicalTrajectory Provable K Machine encode_halt Γ0 n) :=
    PostSplitter_canonicalTrajectory
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) hPSstep Γ0 hPS0
  exact canonicalTrajectory_isSpiral
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
    hRegen Γ0 hPS

end Trajectory

end RevHalt.Trilemma
