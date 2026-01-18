import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_Trajectory

namespace RevHalt.Trilemma

universe u

variable {PropT : Type u}
variable {Code : Type u}

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

end RevHalt.Trilemma
