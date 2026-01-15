import RevHalt.Theory.TheoryDynamics_Transfinite_Jump

/-!
# RevHalt.Theory.TheoryDynamics_Transfinite_JumpFixpoint

Fixpoint derivations from continuity for jump limit operators.
-/

namespace RevHalt

open Set
open Ordinal

section JumpFixpoint

universe u v

variable {PropT : Type u}

theorem jump_fixpoint_from_continuity
    (Cn : Set PropT → Set PropT)
    (J : Set PropT → Set PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hExt : ∀ Γ, Γ ⊆ F Γ) :
    FixpointFromContinuity (PropT := PropT)
      (L := jumpLimitOp (PropT := PropT) Cn J) F A0 lim := by
  intro hCont
  let L := jumpLimitOp (PropT := PropT) Cn J
  let chain : ∀ beta < lim, Set PropT := fun beta _ =>
    transIterL L F A0 beta
  let chainF : ∀ beta < lim, Set PropT := fun beta _ =>
    F (transIterL L F A0 beta)
  let U := preLimit (PropT := PropT) (alpha := lim) chain
  let U' := preLimit (PropT := PropT) (alpha := lim) chainF
  have hUeq : U' = U := by
    ext p
    constructor
    · intro hp
      rcases (mem_preLimit_iff (PropT := PropT) (alpha := lim) chainF p).1 hp with
        ⟨beta, hbeta, hp⟩
      have hsucc : beta + 1 < lim := hLim.succ_lt hbeta
      have hsucc_eq :
          F (transIterL L F A0 beta) = transIterL L F A0 (beta + 1) := by
        simpa using
          (transIterL_succ (L := L) (F := F) (A0 := A0) (alpha := beta)).symm
      have hp' : p ∈ transIterL L F A0 (beta + 1) := by
        simpa [chainF, hsucc_eq] using hp
      have hstage :
          transIterL L F A0 (beta + 1)
            ⊆ preLimit (PropT := PropT) (alpha := lim) chain :=
        stage_subset_preLimit (PropT := PropT) (alpha := lim) chain hsucc
      exact hstage hp'
    · intro hp
      rcases (mem_preLimit_iff (PropT := PropT) (alpha := lim) chain p).1 hp with
        ⟨beta, hbeta, hp⟩
      have hp' : p ∈ F (transIterL L F A0 beta) := hExt _ hp
      exact (mem_preLimit_iff (PropT := PropT) (alpha := lim) chainF p).2
        ⟨beta, hbeta, hp'⟩
  have hCont' :
      F (transIterL L F A0 lim) = Cn (U' ∪ J U') := by
    have h :=
      (continuousAtL_jumpLimitOp_iff (PropT := PropT)
        (Cn := Cn) (J := J) (F := F) (A0 := A0) (lim := lim)).1 hCont
    simpa [L, chainF, U'] using h
  have hLimEq :
      transIterL L F A0 lim = Cn (U ∪ J U) := by
    have h := transIterL_limit (L := L) (F := F) (A0 := A0) (lim := lim) hLim
    simpa [jumpLimitOp_apply, L, chain, U] using h
  have hCont'' : F (transIterL L F A0 lim) = Cn (U ∪ J U) := by
    simpa [hUeq] using hCont'
  simpa [hLimEq.symm] using hCont''

theorem jump_continuousAtL_implies_fixpoint
    (Cn : Set PropT → Set PropT)
    (J : Set PropT → Set PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hExt : ∀ Γ, Γ ⊆ F Γ) :
    ContinuousAtL (PropT := PropT)
      (L := jumpLimitOp (PropT := PropT) Cn J) F A0 lim →
      F (transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 lim) =
        transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 lim := by
  intro hCont
  exact
    jump_fixpoint_from_continuity (PropT := PropT)
      (Cn := Cn) (J := J) (F := F) (A0 := A0)
      (lim := lim) (hLim := hLim) (hExt := hExt) hCont

end JumpFixpoint

section JumpPart7

universe u v
variable {PropT : Type u}
variable {Code : Type u}

variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/-!
## Part 7 endpoint for jump limits
`L := jumpLimitOp Cn J`.
-/

theorem part7_change_of_sense_jump
    (Cn : Set PropT → Set PropT)
    (J  : Set PropT → Set PropT)
    (hMono   : ProvRelMonotone Provable)
    (hCnExt  : CnExtensive (PropT := PropT) Cn)
    (hIdem   : CnIdem (PropT := PropT) Cn)
    (hProvCn : ProvClosedCn (PropT := PropT) Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbsBelow : ∃ β < lim, Absorbable Provable
      (transIterL (jumpLimitOp (PropT := PropT) Cn J)
        (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    (hRouteAt : RouteIIApplies Provable K Machine encode_halt Cn
      (transIterL (jumpLimitOp (PropT := PropT) Cn J)
        (F Provable K Machine encode_halt Cn) A0.Γ lim))
    (hProvClosedAt : ProvClosed Provable
      (transIterL (jumpLimitOp (PropT := PropT) Cn J)
        (F Provable K Machine encode_halt Cn) A0.Γ lim)) :
    ¬ ContinuousAtL (PropT := PropT)
      (L := jumpLimitOp (PropT := PropT) Cn J)
      (F Provable K Machine encode_halt Cn) A0.Γ lim := by
  let F_dyn := F Provable K Machine encode_halt Cn
  have hExtCn :
      ∀ Γ, Γ ⊆ Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := by
    intro Γ
    exact subset_trans Set.subset_union_left (hCnExt (Γ ∪ S1Rel Provable K Machine encode_halt Γ))
  have hExt : ∀ Γ, Γ ⊆ F_dyn Γ := by
    intro Γ
    simpa [F_dyn, F] using hExtCn Γ
  have hFixFromCont :
      FixpointFromContinuity (PropT := PropT)
        (L := jumpLimitOp (PropT := PropT) Cn J) F_dyn A0.Γ lim :=
    jump_fixpoint_from_continuity (PropT := PropT)
      (Cn := Cn) (J := J) (F := F_dyn) (A0 := A0.Γ)
      (lim := lim) (hLim := hLim) (hExt := hExt)
  have hStageIncl :
      LimitIncludesStages (PropT := PropT)
        (jumpLimitOp (PropT := PropT) Cn J) F_dyn A0.Γ :=
    limitIncludesStages_jumpLimitOp (PropT := PropT)
      (Cn := Cn) (J := J) hCnExt
      (F := F_dyn) (A0 := A0.Γ)

  exact structural_escape_at_limit_L (PropT := PropT)
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
    (L := jumpLimitOp (PropT := PropT) Cn J)
    (Cn := Cn) (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
    (A0 := A0) (lim := lim) (hLim := hLim)
    (hAbsBelow := hAbsBelow) (hRouteAt := hRouteAt)
    (hStageIncl := hStageIncl) (hFixFromCont := hFixFromCont) (hProvClosedAt := hProvClosedAt)

end JumpPart7

end RevHalt
