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

/-
Trilemma: it is impossible to have Absorbable at stage 1,
OmegaAdmissible at omega, and RouteIIAt at omega at the same time.
-/
theorem trilemma_not_all
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) :
    ¬ (Absorbable Provable
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
       ∧ OmegaAdmissible Provable Cn
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
       ∧ RouteIIAt Provable K Machine encode_halt
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) := by
  simpa using
    (omega_trilemma_not_all
      (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn)
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (A0 := A0))

end RevHalt.Trilemma
