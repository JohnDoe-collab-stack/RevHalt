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

theorem absorbable1_and_omegaAdmissible_omega_implies_not_routeIIAt_omega
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) :
    Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ ->
    OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) ->
    ¬ RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  intro hA hB hC
  exact (trilemma_not_all (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn) ⟨hA, ⟨hB, hC⟩⟩

theorem absorbable1_and_routeIIAt_omega_implies_not_omegaAdmissible_omega
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) :
    Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ ->
    RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) ->
    ¬ OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  intro hA hC hB
  exact (trilemma_not_all (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn) ⟨hA, ⟨hB, hC⟩⟩

theorem omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable1
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) :
    OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) ->
    RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) ->
    ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ := by
  intro hB hC hA
  exact (trilemma_not_all (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn) ⟨hA, ⟨hB, hC⟩⟩

theorem trilemma_not_all_at_step
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    ¬ (Absorbable Provable
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ
       ∧ OmegaAdmissible Provable Cn
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n))
       ∧ RouteIIAt Provable K Machine encode_halt
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n))) := by
  simpa [chainState_succ] using
    (trilemma_not_all (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn)
      (A0 := chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)
      hMono hCnExt hIdem hProvCn)

theorem absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ ->
    OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) ->
    ¬ RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) := by
  intro hA hB hC
  exact (trilemma_not_all_at_step (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn n) ⟨hA, ⟨hB, hC⟩⟩

theorem absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ ->
    RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) ->
    ¬ OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) := by
  intro hA hC hB
  exact (trilemma_not_all_at_step (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn n) ⟨hA, ⟨hB, hC⟩⟩

theorem omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (n : Nat) :
    OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) ->
    RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)) ->
    ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ := by
  intro hB hC hA
  exact (trilemma_not_all_at_step (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hMono hCnExt hIdem hProvCn n) ⟨hA, ⟨hB, hC⟩⟩

end RevHalt.Trilemma
