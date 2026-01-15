import RevHalt.Theory.TheoryDynamics
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Common

/-!
# RevHalt.Theory.TheoryDynamics_Transfinite_Fixed

This module extends the core dynamics to transfinite ordinals.
It isolates the ordinal-indexed chains and cardinal arguments.
-/

namespace RevHalt

open Set
open Ordinal

section TransfiniteDynamics

universe u v

variable {PropT : Type u}

/--
  **Transfinite Union (Independent)**:
  The union of a global chain up to a limit.
-/
def transUnion (chain : Ordinal.{v} → Set PropT) (lim : Ordinal.{v}) : Set PropT :=
  { p | ∃ β, β < lim ∧ p ∈ chain β }

/--
  **Transfinite Union (Family)**:
  Helper for recursion, taking a dependent family.
-/
def transUnionFamily {α : Ordinal.{v}} (chain : ∀ β < α, Set PropT) : Set PropT :=
  { p | ∃ β, ∃ (h : β < α), p ∈ chain β h }

/-- **Limit Operator**: parameterized limit constructor for transfinite recursion. -/
structure LimitOp (PropT : Type u) where
  apply : ∀ {alpha : Ordinal.{v}}, (∀ beta < alpha, Set PropT) -> Set PropT

/-- **Limit Decomposition**: factor a limit rule through a global chain. -/
structure LimitDecomp (L : LimitOp PropT) : Type (max u (v + 1)) where
  decomp :
    ∀ {alpha : Ordinal.{v}}, (∀ beta < alpha, Set PropT) -> Ordinal.{v} -> Set PropT
  decomp_spec :
    ∀ {alpha : Ordinal.{v}} (_hLim : Order.IsSuccLimit alpha)
      (chain : ∀ beta < alpha, Set PropT),
      L.apply chain = transUnion (decomp chain) alpha
  decomp_sub :
    ∀ {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) {beta : Ordinal.{v}}
      (hbeta : beta < alpha),
      chain beta hbeta ⊆ decomp chain beta

/-- Union limit operator (the current default). -/
def unionLimitOp : LimitOp PropT :=
  { apply := fun {alpha} chain => transUnionFamily (α := alpha) chain }

/-- Global = closure after union; the limit stage can add consequences. -/
def cnUnionLimitOp (Cn : Set PropT → Set PropT) : LimitOp PropT :=
  { apply := fun {alpha} chain => Cn (transUnionFamily (α := alpha) chain) }

@[simp]
theorem cnUnionLimitOp_apply
    (Cn : Set PropT → Set PropT)
    {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) :
    (cnUnionLimitOp (PropT := PropT) Cn).apply (alpha := alpha) chain =
      Cn (transUnionFamily (α := alpha) chain) := rfl

theorem chain_proof_irrel
    {alpha : Ordinal.{v}}
    (chain : ∀ beta < alpha, Set PropT)
    {beta : Ordinal.{v}} (h1 h2 : beta < alpha) :
    chain beta h1 = chain beta h2 := by
  cases (Subsingleton.elim h1 h2)
  rfl

def limitDecomp_union : LimitDecomp (L := (unionLimitOp (PropT := PropT))) := by
  classical
  refine
    { decomp := ?decomp
      decomp_spec := ?spec
      decomp_sub := ?sub }
  · intro alpha chain beta
    by_cases h : beta < alpha
    · exact chain beta h
    · exact ∅
  · intro alpha _hLim chain
    ext p
    have hmem_apply :
        p ∈ (unionLimitOp (PropT := PropT)).apply (alpha := alpha) chain ↔
          ∃ beta, ∃ h : beta < alpha, p ∈ chain beta h := by
      simp [unionLimitOp, transUnionFamily]
    constructor
    · intro hp
      rcases hmem_apply.mp hp with ⟨beta, hbeta, hp⟩
      refine ⟨beta, hbeta, ?_⟩
      by_cases h : beta < alpha
      · have hset : chain beta hbeta = chain beta h := (chain_proof_irrel (PropT := PropT) chain hbeta h).symm
        have hmem : p ∈ chain beta h := by
          simpa [hset] using hp
        simpa [h] using hmem
      · exact (False.elim (h hbeta))
    · intro hp
      rcases hp with ⟨beta, hbeta, hp⟩
      have hmem : p ∈ chain beta hbeta := by
        by_cases h : beta < alpha
        · have hset : chain beta h = chain beta hbeta :=
            chain_proof_irrel (PropT := PropT) chain h hbeta
          have hmem' : p ∈ chain beta h := by
            simpa [h] using hp
          simpa [hset] using hmem'
        · exact (False.elim (h hbeta))
      exact hmem_apply.mpr ⟨beta, hbeta, hmem⟩
  · intro alpha chain beta hbeta p hp
    by_cases h : beta < alpha
    · have hset : chain beta h = chain beta hbeta :=
        chain_proof_irrel (PropT := PropT) chain h hbeta
      simpa [h, hset] using hp
    · exact (False.elim (h hbeta))

/--
  **Transfinite Iteration (Parametric Limit)**:
  Recursively defines the state Gamma_alpha for any ordinal alpha, using a limit operator.
-/
def transIterL
    (L : LimitOp PropT)
    (F : Set PropT -> Set PropT)
    (A0 : Set PropT)
    (alpha : Ordinal.{v}) : Set PropT :=
  Ordinal.limitRecOn alpha
    A0
    (fun _ prev => F prev)
    (fun _ _ chain => L.apply chain)

@[simp]
theorem transIterL_zero (L : LimitOp PropT) (F : Set PropT -> Set PropT) (A0 : Set PropT) :
    transIterL L F A0 0 = A0 :=
  Ordinal.limitRecOn_zero _ _ _

@[simp]
theorem transIterL_succ (L : LimitOp PropT) (F : Set PropT -> Set PropT)
    (A0 : Set PropT) (alpha : Ordinal.{v}) :
    transIterL L F A0 (alpha + 1) = F (transIterL L F A0 alpha) :=
  Ordinal.limitRecOn_succ _ _ _ _

theorem transIterL_limit
    (L : LimitOp PropT)
    (F : Set PropT -> Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim) :
    transIterL L F A0 lim =
      L.apply (alpha := lim) (fun beta (_hbeta : beta < lim) => transIterL L F A0 beta) := by
  unfold transIterL
  simp only [Ordinal.limitRecOn_limit _ _ _ _ hLim]

/--
  **Transfinite Iteration**:
  Recursively defines the state Γ_α for any ordinal α.
-/
abbrev transIter (F : Set PropT → Set PropT) (A0 : Set PropT) (α : Ordinal.{v}) : Set PropT :=
  transIterL unionLimitOp F A0 α

-- ═══════════════════════════════════════════════════════════════════════════════
-- RECURSION LEMMAS (Using + 1)
-- ═══════════════════════════════════════════════════════════════════════════════

@[simp]
theorem transIter_zero (F : Set PropT → Set PropT) (A0 : Set PropT) :
    transIter F A0 0 = A0 :=
  by
    simp [transIter, transIterL_zero]

@[simp]
theorem transIter_succ (F : Set PropT → Set PropT) (A0 : Set PropT) (α : Ordinal.{v}) :
    transIter F A0 (α + 1) = F (transIter F A0 α) :=
  by
    change
      transIterL unionLimitOp F A0 (α + 1) =
        F (transIterL unionLimitOp F A0 α)
    simpa using
      (transIterL_succ (L := unionLimitOp) (F := F) (A0 := A0) (alpha := α))

theorem transIter_limit
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim) :
    transIter F A0 lim = transUnion (transIter F A0) lim := by
  have hEq :
      transIter F A0 lim =
        transUnionFamily (α := lim) (fun β (_hβ : β < lim) => transIter F A0 β) := by
    simpa [transIter, unionLimitOp] using
      (transIterL_limit (L := unionLimitOp) (F := F) (A0 := A0) (lim := lim) hLim)
  rw [hEq]
  dsimp [transUnion, transUnionFamily]
  ext p
  constructor
  · rintro ⟨β, hβ, hp⟩; exact ⟨β, hβ, hp⟩
  · rintro ⟨β, hβ, hp⟩; exact ⟨β, hβ, hp⟩

/-- Local property: at any limit, earlier stages embed into the limit state. -/
def LimitIncludesStages (L : LimitOp PropT) (F : Set PropT -> Set PropT) (A0 : Set PropT) : Prop :=
  ∀ {lim : Ordinal.{v}} (_hLim : Order.IsSuccLimit lim) {β : Ordinal.{v}} (_hβ : β < lim),
    transIterL L F A0 β ⊆ transIterL L F A0 lim

theorem limitIncludesStages_of_decomp
    (L : LimitOp PropT)
    (hDecomp : LimitDecomp (L := L))
    (F : Set PropT -> Set PropT)
    (A0 : Set PropT) :
    LimitIncludesStages L F A0 := by
  intro lim hLim beta hbeta p hp
  let chain : ∀ gamma < lim, Set PropT := fun gamma _hgamma => transIterL L F A0 gamma
  have hIterEq :
      transIterL L F A0 lim =
        L.apply (alpha := lim) (fun gamma (_hgamma : gamma < lim) => transIterL L F A0 gamma) := by
    simpa using (transIterL_limit (L := L) (F := F) (A0 := A0) (lim := lim) hLim)
  have hEq : L.apply chain = transUnion (hDecomp.decomp chain) lim :=
    hDecomp.decomp_spec hLim chain
  have hSub : chain beta hbeta ⊆ hDecomp.decomp chain beta :=
    hDecomp.decomp_sub chain hbeta
  have hMem : p ∈ hDecomp.decomp chain beta := hSub hp
  have hMemUnion : p ∈ transUnion (hDecomp.decomp chain) lim := ⟨beta, hbeta, hMem⟩
  have hMemApply : p ∈ L.apply chain := by
    rw [hEq]
    exact hMemUnion
  rw [hIterEq]
  exact hMemApply

/-- `unionLimitOp` satisfies stage-inclusion via `LimitDecomp`. -/
theorem limitIncludesStages_union (F : Set PropT -> Set PropT) (A0 : Set PropT) :
    LimitIncludesStages (PropT := PropT) unionLimitOp F A0 :=
  limitIncludesStages_of_decomp (L := unionLimitOp) (limitDecomp_union (PropT := PropT)) F A0

-- ═══════════════════════════════════════════════════════════════════════════════
-- MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Transfinite Monotonicity**:
  If F is extensive (Γ ⊆ F(Γ)), then the transfinite iteration is monotone.
-/
theorem transIter_mono
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hExt : ∀ Γ, Γ ⊆ F Γ) :
    Monotone (transIter F A0) := by
  intro α β hle
  revert α
  refine @Ordinal.limitRecOn (fun β => ∀ α, α ≤ β → transIter F A0 α ⊆ transIter F A0 β) β ?_ ?_ ?_
  · intro α hle
    -- α ≤ 0 => α = 0
    have : α = 0 := by
      simpa [nonpos_iff_eq_zero] using hle
    subst this
    exact le_rfl
  · intro γ ih α hle
    -- goal: Γ_α ⊆ Γ_{γ+1} = F(Γ_γ)
    have hsucc : transIter F A0 (γ + 1) = F (transIter F A0 γ) := by
      simpa using (transIter_succ F A0 γ)
    -- split α ≤ γ+1 into α < γ+1 or α = γ+1
    rcases lt_or_eq_of_le hle with hlt | rfl
    · have hleγ : α ≤ γ := Order.lt_succ_iff.mp hlt
      have hsub : transIter F A0 α ⊆ transIter F A0 γ := ih α hleγ
      -- Γ_α ⊆ Γ_γ ⊆ F(Γ_γ)
      rw [← Ordinal.add_one_eq_succ, hsucc]
      exact subset_trans hsub (hExt (transIter F A0 γ))
    · -- α = γ+1
      -- Γ_{γ+1} ⊆ Γ_{γ+1}
      simp [hsucc, ← Ordinal.add_one_eq_succ]
  · intro lim hLim ih α hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · -- α < lim => Γ_α ⊆ ⋃_{β<lim} Γ_β
      rw [transIter_limit F A0 lim hLim]
      intro p hp
      exact ⟨α, hlt, hp⟩
    · exact Subset.rfl

end TransfiniteDynamics

section TransfiniteTheorems

universe u v
variable {PropT : Type u}
variable {Code : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/-- **FrontierInjected(F)**: frontier sentences are injected into the next state.
    This is the key structural property: S1Rel(Γ) ⊆ F(Γ). -/
def FrontierInjected (F : Set PropT → Set PropT) : Prop :=
  ∀ Γ : Set PropT, S1Rel Provable K Machine encode_halt Γ ⊆ F Γ

/-- FrontierInjected holds for F = Cn(Γ ∪ S1Rel Γ) when Cn is extensive. -/
theorem frontierInjected_of_CnExt
    (Cn : Set PropT → Set PropT)
    (hCnExt : CnExtensive Cn) :
    FrontierInjected Provable K Machine encode_halt
      (fun Γ => Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ)) := by
  intro Γ p hp
  have : p ∈ (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := Or.inr hp
  exact hCnExt (Γ ∪ S1Rel Provable K Machine encode_halt Γ) this

/-- Continuity at a limit (union form). -/
def ContinuousAt (F : Set PropT → Set PropT) (A0 : Set PropT) (lim : Ordinal.{v}) : Prop :=
  F (transIter F A0 lim) = transUnion (fun β' => F (transIter F A0 β')) lim

/-- Admissibility at a limit stage. -/
def AdmissibleAtLimit
    (Cn : Set PropT → Set PropT)
    (F_dyn : Set PropT → Set PropT)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v}) : Prop :=
  OmegaAdmissible Provable Cn (transIter F_dyn A0.Γ lim)

/-- Limit collapse schema (L-version), using stage-inclusion at limits. -/
theorem limit_collapse_schema_L
    (L : LimitOp PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hMono : ProvRelMonotone Provable)
    (_hExt : ∀ Γ, Γ ⊆ F Γ)
    (hInj : FrontierInjected Provable K Machine encode_halt F)
    (hStage : LimitIncludesStages (PropT := PropT) L F A0)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable (transIterL L F A0 (β + 1))) :
    S1Rel Provable K Machine encode_halt (transIterL L F A0 lim) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp

  obtain ⟨β, hβlt, hAbsβ⟩ := hAbs
  rcases hp with ⟨e, rfl, hKit, hNprov_lim⟩

  have hSub_β_lim : transIterL L F A0 β ⊆ transIterL L F A0 lim :=
    hStage hLim hβlt

  have hSuccLt : β + 1 < lim := hLim.succ_lt hβlt
  have hSub_succ_lim : transIterL L F A0 (β + 1) ⊆ transIterL L F A0 lim :=
    hStage hLim hSuccLt

  have hNprov_β : ¬ Provable (transIterL L F A0 β) (encode_halt e) := by
    intro hPβ
    have hPlim : Provable (transIterL L F A0 lim) (encode_halt e) :=
      hMono _ _ hSub_β_lim _ hPβ
    exact hNprov_lim hPlim

  have hS1β : encode_halt e ∈ S1Rel Provable K Machine encode_halt (transIterL L F A0 β) :=
    ⟨e, rfl, hKit, hNprov_β⟩

  have hMem_succ : encode_halt e ∈ transIterL L F A0 (β + 1) := by
    have hinj : encode_halt e ∈ F (transIterL L F A0 β) := hInj _ hS1β
    rw [transIterL_succ (L := L) (F := F) (A0 := A0) (alpha := β)]
    exact hinj

  have hP_succ : Provable (transIterL L F A0 (β + 1)) (encode_halt e) :=
    hAbsβ (encode_halt e) hMem_succ

  have hP_lim : Provable (transIterL L F A0 lim) (encode_halt e) :=
    hMono _ _ hSub_succ_lim _ hP_succ

  exact hNprov_lim hP_lim

theorem limit_collapse_schema_Decomp
    (L : LimitOp PropT)
    (hDecomp : LimitDecomp (L := L))
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hMono : ProvRelMonotone Provable)
    (_hExt : ∀ Γ, Γ ⊆ F Γ)
    (hInj : FrontierInjected Provable K Machine encode_halt F)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable (transIterL L F A0 (β + 1))) :
    S1Rel Provable K Machine encode_halt (transIterL L F A0 lim) = ∅ :=
  limit_collapse_schema_L Provable K Machine encode_halt
    (L := L) (F := F) (A0 := A0)
    (hMono := hMono) (_hExt := _hExt) (hInj := hInj)
    (hStage := limitIncludesStages_of_decomp (L := L) hDecomp F A0)
    (lim := lim) (hLim := hLim) (hAbs := hAbs)

/--
  **Limit Collapse Schema** (Corrected):
  If there is an absorption point below a limit, the frontier at the limit is empty.

  The key insight: a frontier element p at lim would have been:
  1. Also in S1Rel(Γ_β) by monotonicity of Provable (contrapositive)
  2. Injected into Γ_{β+1} by FrontierInjected
  3. Made provable at Γ_{β+1} by Absorbable
  4. Hence provable at Γ_lim by monotonicity
  5. Contradiction with p ∈ S1Rel(Γ_lim)
-/
theorem limit_collapse_schema
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hExt : ∀ Γ, Γ ⊆ F Γ)
    (hInj : FrontierInjected Provable K Machine encode_halt F)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable (transIter F A0 (β + 1))) :
    S1Rel Provable K Machine encode_halt (transIter F A0 lim) = ∅ := by
  simpa [transIter] using
    (limit_collapse_schema_L Provable K Machine encode_halt
      (L := unionLimitOp) (F := F) (A0 := A0)
      (hMono := hMono) (_hExt := hExt) (hInj := hInj)
      (hStage := limitIncludesStages_union (PropT := PropT) (F := F) (A0 := A0))
      (lim := lim) (hLim := hLim) (hAbs := hAbs))

/--
  **Limit Fixpoint Property**:
  If F is extensive and continuous at λ, then Γ_λ is a fixpoint.
-/
theorem continuous_implies_fixpoint_at_limit
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hExt : ∀ Γ, Γ ⊆ F Γ)
    (limOrd : Ordinal.{v})
    (hLim : Order.IsSuccLimit limOrd)
    -- Continuity hypothesis
    (hCont : ContinuousAt (PropT := PropT) F A0 limOrd) :
    F (transIter F A0 limOrd) = transIter F A0 limOrd := by
  rw [hCont]
  -- RHS is ∪_{β<limOrd} Γ_{β+1}
  rw [transIter_limit F A0 limOrd hLim]
  -- Show ∪_{β<limOrd} F(Γ_β) = ∪_{β<limOrd} Γ_β
  dsimp [transUnion]
  ext p
  constructor
  · rintro ⟨β, hβ, hp⟩
    -- p ∈ F(Γ_β) = Γ_{β+1}.
    have hSuccLt : β + 1 < limOrd := hLim.succ_lt hβ
    rw [← transIter_succ F A0 β] at hp
    exact ⟨β + 1, hSuccLt, hp⟩
  · rintro ⟨β, hβ, hp⟩
    -- p ∈ Γ_β. Need to show ∃ β', β' < limOrd ∧ p ∈ F(Γ_{β'})
    -- p ∈ Γ_β ⊆ F(Γ_β) by extensivity hExt
    have hInF : p ∈ F (transIter F A0 β) := hExt (transIter F A0 β) hp
    exact ⟨β, hβ, hInF⟩

/-! Escape (L-version): takes fixpoint and ProvClosed at lim as local hypotheses. -/
theorem structural_escape_transfinite_L
    (L : LimitOp PropT)
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (_hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim))
    (hStage : LimitIncludesStages (PropT := PropT) L (F Provable K Machine encode_halt Cn) A0.Γ)
    (hFix : (F Provable K Machine encode_halt Cn)
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim) =
        transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim)
    (hProvClosed_lim : ProvClosed Provable
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim)) :
    False := by
  let F_dyn := F Provable K Machine encode_halt Cn
  let Γ_lim : Set PropT := transIterL L F_dyn A0.Γ lim
  let S_lim : Set PropT := S1Rel Provable K Machine encode_halt Γ_lim

  have hFix_symm : Γ_lim = Cn (Γ_lim ∪ S_lim) := by
    simpa [Γ_lim, S_lim, F_dyn, F] using hFix.symm

  have hCnClosed : Cn Γ_lim = Γ_lim := by
    have hStep1 : Cn Γ_lim = Cn (Cn (Γ_lim ∪ S_lim)) := congrArg Cn hFix_symm
    have hStep2 : Cn (Cn (Γ_lim ∪ S_lim)) = Cn (Γ_lim ∪ S_lim) := hIdem (Γ_lim ∪ S_lim)
    have hStep3 : Cn (Γ_lim ∪ S_lim) = Γ_lim := hFix_symm.symm
    rw [hStep1, hStep2, hStep3]

  have hAdm : OmegaAdmissible Provable Cn Γ_lim := ⟨hCnClosed, hProvClosed_lim⟩

  have hNonEmpty : S1Rel Provable K Machine encode_halt Γ_lim ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp (hRoute hAdm)

  have hFExt : ∀ Γ, Γ ⊆ F_dyn Γ := fun Γ =>
    subset_trans Set.subset_union_left (hCnExt _)

  have hInj : FrontierInjected Provable K Machine encode_halt F_dyn :=
    frontierInjected_of_CnExt Provable K Machine encode_halt Cn hCnExt

  have hEmpty : S1Rel Provable K Machine encode_halt Γ_lim = ∅ :=
    limit_collapse_schema_L Provable K Machine encode_halt
      (L := L) (F := F_dyn) (A0 := A0.Γ)
      (hMono := hMono) (_hExt := hFExt) (hInj := hInj) (hStage := hStage)
      (lim := lim) (hLim := hLim) (hAbs := hAbs)

  exact hNonEmpty hEmpty

/-- ProvClosed preserved by increasing ordinal unions below a limit.
    This is the ordinal generalization of ProvClosedDirected. -/
def ProvClosedDirectedOrd : Prop :=
  ∀ (chain : Ordinal.{v} → Set PropT) (lim : Ordinal.{v}),
    (∀ β, β < lim → ProvClosed Provable (chain β)) →
    (∀ {α β}, α ≤ β → chain α ⊆ chain β) →
    ProvClosed Provable (transUnion chain lim)

/-- ProvClosed along the full transfinite iteration:
    0: given by h0
    succ: given by hProvCn
    limit: given by ProvClosedDirectedOrd on transUnion -/
theorem transIter_provClosed
    (hPC : ProvClosedDirectedOrd.{u, v} Provable)
    (Cn : Set PropT → Set PropT)
    (hProvCn : ProvClosedCn Provable Cn)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hExt : ∀ Γ, Γ ⊆ F Γ)
    (h0 : ProvClosed Provable A0)
    (hF_eq : ∀ Γ, F Γ = Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ)) :
    ∀ α : Ordinal.{v}, ProvClosed Provable (transIter F A0 α) := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero =>
      simpa using h0
  | succ γ ih =>
      -- Γ_{γ+1} = F(Γ_γ) = Cn(...)
      rw [← Ordinal.add_one_eq_succ]
      have : transIter F A0 (γ + 1) = F (transIter F A0 γ) := by
        simpa using (transIter_succ F A0 γ)
      -- rewrite to Cn form then use hProvCn
      rw [this, hF_eq]
      exact hProvCn (transIter F A0 γ ∪ S1Rel Provable K Machine encode_halt (transIter F A0 γ))
  | limit lim hLim ih =>
      -- Γ_lim = transUnion (Γ_β)_{β<lim}
      rw [transIter_limit F A0 lim hLim]
      have hmonoIter : Monotone (transIter F A0) := transIter_mono F A0 hExt
      exact hPC (transIter F A0) lim
        (fun β hβ => ih β hβ)
        (by
          intro α β hle
          exact hmonoIter hle)

end TransfiniteTheorems

section TransfiniteEscape

universe u v
variable {PropT : Type u}
variable {Code : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/--
  **Transfinite Structural Escape**:
  The canonical contradiction:
  1. Continuity at limit implies Fixpoint.
  2. Fixpoint implies Admissibility (using algebraic properties of Cn).
  3. Admissibility + Route II implies S1Rel ≠ ∅.
  4. Absorption below limit implies S1Rel = ∅ (Limit Collapse).
  5. Contradiction.

  Thus, F cannot be continuous at any limit ordinal where absorption has occurred previously.
-/
theorem structural_escape_transfinite
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCord : ProvClosedDirectedOrd.{u, v} Provable) -- Ordinal version
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    -- Hyp 1: Absorption at some predecessor
    (hAbs : ∃ β < lim, Absorbable Provable (transIter (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    -- Hyp 2: Route II at limit
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
              (transIter (F Provable K Machine encode_halt Cn) A0.Γ lim))
    -- Hyp 3: Continuity
    (hCont : ContinuousAt (PropT := PropT)
      (F Provable K Machine encode_halt Cn) A0.Γ lim) :
    False := by
  let F_dyn := F Provable K Machine encode_halt Cn

  -- 1. Continuity => Fixpoint
  have hFExt : ∀ Γ, Γ ⊆ F_dyn Γ := fun Γ =>
    (subset_trans Set.subset_union_left (hCnExt _))
  have hFix : F_dyn (transIter F_dyn A0.Γ lim) = transIter F_dyn A0.Γ lim :=
    continuous_implies_fixpoint_at_limit F_dyn A0.Γ hFExt lim hLim hCont

  -- 2. Fixpoint => Admissibility
  let Γ_lim := transIter F_dyn A0.Γ lim
  let S_lim := S1Rel Provable K Machine encode_halt Γ_lim

  -- Cn-closed from fixpoint
  have hFix_symm : Γ_lim = Cn (Γ_lim ∪ S_lim) := by
    symm; simpa [F_dyn, F, S_lim] using hFix

  have hCnClosed : Cn Γ_lim = Γ_lim := by
    have hStep1 : Cn Γ_lim = Cn (Cn (Γ_lim ∪ S_lim)) := congrArg Cn hFix_symm
    have hStep2 : Cn (Cn (Γ_lim ∪ S_lim)) = Cn (Γ_lim ∪ S_lim) := hIdem (Γ_lim ∪ S_lim)
    have hStep3 : Cn (Γ_lim ∪ S_lim) = Γ_lim := hFix_symm.symm
    rw [hStep1, hStep2, hStep3]

  -- ProvClosed at lim via uniform transfinite lemma
  have hF_eq : ∀ Γ, F_dyn Γ = Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := fun _ => rfl

  have hProvClosed_lim : ProvClosed Provable Γ_lim :=
    transIter_provClosed (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (hPC := hPCord) (Cn := Cn) (hProvCn := hProvCn) (F := F_dyn) (A0 := A0.Γ)
      (hExt := hFExt) (h0 := A0.prov_closed) (hF_eq := hF_eq) lim

  have hAdm : OmegaAdmissible Provable Cn Γ_lim := ⟨hCnClosed, hProvClosed_lim⟩

  -- 3. Admissibility => S1 ≠ ∅
  have hNonEmpty : S1Rel Provable K Machine encode_halt Γ_lim ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp (hRoute hAdm)

  -- 4. Absorption => S1 = ∅ (via FrontierInjected + limit_collapse_schema)
  have hInj : FrontierInjected Provable K Machine encode_halt F_dyn :=
    frontierInjected_of_CnExt Provable K Machine encode_halt Cn hCnExt
  have hEmpty : S1Rel Provable K Machine encode_halt Γ_lim = ∅ :=
    limit_collapse_schema Provable K Machine encode_halt F_dyn A0.Γ hMono hFExt hInj lim hLim hAbs

  contradiction

theorem structural_escape_at_limit
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCord : ProvClosedDirectedOrd.{u, v} Provable)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable (transIter (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
              (transIter (F Provable K Machine encode_halt Cn) A0.Γ lim)) :
    ¬ ContinuousAt (PropT := PropT) (F Provable K Machine encode_halt Cn) A0.Γ lim := by
  intro hCont
  exact structural_escape_transfinite (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt) Cn hMono hCnExt hIdem hProvCn hPCord A0 lim hLim hAbs hRoute hCont

/-! ## Part 7 API -/

/-- Continuity at a limit (parametric L form). -/
def ContinuousAtL
    (L : LimitOp PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v}) : Prop :=
  F (transIterL L F A0 lim) =
    L.apply (alpha := lim) (fun beta (_ : beta < lim) => F (transIterL L F A0 beta))

/-!
A global `L` is a limit operator.
Continuity at the limit is `ContinuousAtL`.
Part 7 does not assume continuity implies a fixpoint; it requires it via `FixpointFromContinuity`.
The escape theorem then forces ¬ continuity under the dynamic hypotheses.
-/
def FixpointFromContinuity
    (L : LimitOp PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal.{v}) : Prop :=
  ContinuousAtL (L := L) F A0 lim →
    F (transIterL L F A0 lim) = transIterL L F A0 lim

theorem structural_escape_at_limit_L
    (L : LimitOp PropT)
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbsBelow : ∃ β < lim, Absorbable Provable
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    (hRouteAt : RouteIIApplies Provable K Machine encode_halt Cn
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim))
    (hStageIncl : LimitIncludesStages.{u, v} (PropT := PropT) L
      (F Provable K Machine encode_halt Cn) A0.Γ)
    (hFixFromCont : FixpointFromContinuity (PropT := PropT) (L := L)
      (F Provable K Machine encode_halt Cn) A0.Γ lim)
    (hProvClosedAt : ProvClosed Provable
      (transIterL L (F Provable K Machine encode_halt Cn) A0.Γ lim)) :
    ¬ ContinuousAtL (PropT := PropT) (L := L)
      (F Provable K Machine encode_halt Cn) A0.Γ lim := by
  intro hCont
  have hFix :=
    hFixFromCont hCont
  exact structural_escape_transfinite_L (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt) (L := L) (Cn := Cn)
    (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (_hProvCn := hProvCn)
    (A0 := A0) (lim := lim) (hLim := hLim) (hAbs := hAbsBelow) (hRoute := hRouteAt)
    (hStage := hStageIncl) (hFix := hFix) (hProvClosed_lim := hProvClosedAt)

theorem global_change_of_sense
    (Cn : Set PropT → Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbsBelow : ∃ β < lim, Absorbable Provable
      (transIterL (cnUnionLimitOp (PropT := PropT) Cn)
        (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    (hRouteAt : RouteIIApplies Provable K Machine encode_halt Cn
      (transIterL (cnUnionLimitOp (PropT := PropT) Cn)
        (F Provable K Machine encode_halt Cn) A0.Γ lim))
    (hStageIncl : LimitIncludesStages.{u, v} (PropT := PropT)
      (cnUnionLimitOp (PropT := PropT) Cn)
      (F Provable K Machine encode_halt Cn) A0.Γ)
    (hFixFromCont : FixpointFromContinuity (PropT := PropT)
      (L := cnUnionLimitOp (PropT := PropT) Cn)
      (F Provable K Machine encode_halt Cn) A0.Γ lim)
    (hProvClosedAt : ProvClosed Provable
      (transIterL (cnUnionLimitOp (PropT := PropT) Cn)
        (F Provable K Machine encode_halt Cn) A0.Γ lim)) :
    ¬ ContinuousAtL (PropT := PropT)
      (L := cnUnionLimitOp (PropT := PropT) Cn)
      (F Provable K Machine encode_halt Cn) A0.Γ lim :=
  structural_escape_at_limit_L (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt) (L := cnUnionLimitOp (PropT := PropT) Cn)
    (Cn := Cn) (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem)
    (hProvCn := hProvCn) (A0 := A0) (lim := lim) (hLim := hLim)
    (hAbsBelow := hAbsBelow) (hRouteAt := hRouteAt) (hStageIncl := hStageIncl)
    (hFixFromCont := hFixFromCont) (hProvClosedAt := hProvClosedAt)

end TransfiniteEscape

end RevHalt
