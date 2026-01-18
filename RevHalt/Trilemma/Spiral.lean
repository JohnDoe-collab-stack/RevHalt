import RevHalt.Theory.TheoryDynamics

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
  exact strict_chainState_step Provable K Machine encode_halt Cn
    hCnExt hIdem hProvCn A0 n hPS hW

/-- Spiral step: monotone extension for every n. -/
theorem spiral_step_mono
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ
      ⊆
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ := by
  exact chainState_step_hom_def Provable K Machine encode_halt Cn
    hCnExt hIdem hProvCn A0 n

end RevHalt.Trilemma
