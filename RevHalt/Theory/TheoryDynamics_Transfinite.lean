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

universe u

variable {PropT : Type u}

/--
  **Transfinite Union (Independent)**:
  The union of a global chain up to a limit.
-/
def transUnion (chain : Ordinal → Set PropT) (lim : Ordinal) : Set PropT :=
  { p | ∃ β, β < lim ∧ p ∈ chain β }

/--
  **Transfinite Union (Family)**:
  Helper for recursion, taking a dependent family.
-/
def transUnionFamily {α : Ordinal} (chain : ∀ β < α, Set PropT) : Set PropT :=
  { p | ∃ β, ∃ (h : β < α), p ∈ chain β h }

/--
  **Transfinite Iteration**:
  Recursively defines the state Γ_α for any ordinal α.
-/
def transIter
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (α : Ordinal) : Set PropT :=
  Ordinal.limitRecOn α
    A0
    (fun _ prev => F prev)
    (fun _ _ chain => transUnionFamily chain)

-- ═══════════════════════════════════════════════════════════════════════════════
-- RECURSION LEMMAS (Using + 1)
-- ═══════════════════════════════════════════════════════════════════════════════

@[simp]
theorem transIter_zero (F : Set PropT → Set PropT) (A0 : Set PropT) :
    transIter F A0 0 = A0 :=
  Ordinal.limitRecOn_zero _ _ _

@[simp]
theorem transIter_succ (F : Set PropT → Set PropT) (A0 : Set PropT) (α : Ordinal) :
    transIter F A0 (α + 1) = F (transIter F A0 α) :=
  Ordinal.limitRecOn_succ _ _ _ _

theorem transIter_limit
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (lim : Ordinal)
    (hLim : Order.IsSuccLimit lim) :
    transIter F A0 lim = transUnion (transIter F A0) lim := by
  unfold transIter
  simp only [Ordinal.limitRecOn_limit _ _ _ _ hLim]
  dsimp [transUnion, transUnionFamily]
  ext p
  constructor
  · rintro ⟨β, hβ, hp⟩; exact ⟨β, hβ, hp⟩
  · rintro ⟨β, hβ, hp⟩; exact ⟨β, hβ, hp⟩

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

variable {PropT : Type u}
universe v
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
    (lim : Ordinal)
    (hLim : Order.IsSuccLimit lim)
    (hAbs : ∃ β < lim, Absorbable Provable (transIter F A0 (β + 1))) :
    S1Rel Provable K Machine encode_halt (transIter F A0 lim) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp

  -- pick the absorption witness
  obtain ⟨β, hβlt, hAbsβ⟩ := hAbs

  -- Unpack hp at lim: p = encode_halt e, kit, and not provable at lim
  rcases hp with ⟨e, rfl, hKit, hNprov_lim⟩

  -- Need monotonicity of transIter to compare stages
  have hmono : Monotone (transIter F A0) :=
    transIter_mono F A0 hExt

  have hSub_β_lim : transIter F A0 β ⊆ transIter F A0 lim :=
    hmono (le_of_lt hβlt)

  have hSuccLt : β + 1 < lim := hLim.succ_lt hβlt
  have hSub_succ_lim : transIter F A0 (β + 1) ⊆ transIter F A0 lim :=
    hmono (le_of_lt hSuccLt)

  -- From ¬Provable at lim, infer ¬Provable at stage β by contrapositive
  have hNprov_β : ¬ Provable (transIter F A0 β) (encode_halt e) := by
    intro hPβ
    have hPlim : Provable (transIter F A0 lim) (encode_halt e) :=
      hMono _ _ hSub_β_lim _ hPβ
    exact hNprov_lim hPlim

  -- Hence encode_halt e is in S1Rel at stage β
  have hS1β : encode_halt e ∈ S1Rel Provable K Machine encode_halt (transIter F A0 β) :=
    ⟨e, rfl, hKit, hNprov_β⟩

  -- Frontier injection: S1Rel(Γβ) ⊆ F(Γβ) = Γ_{β+1}
  have hMem_succ : encode_halt e ∈ transIter F A0 (β + 1) := by
    have hinj : encode_halt e ∈ F (transIter F A0 β) := hInj _ hS1β
    rw [transIter_succ]
    exact hinj

  -- Absorbable at stage β+1 gives provable at stage β+1
  have hP_succ : Provable (transIter F A0 (β + 1)) (encode_halt e) :=
    hAbsβ (encode_halt e) hMem_succ

  -- then provable at lim by monotonicity
  have hP_lim : Provable (transIter F A0 lim) (encode_halt e) :=
    hMono _ _ hSub_succ_lim _ hP_succ

  -- contradiction
  exact hNprov_lim hP_lim

/--
  **Limit Fixpoint Property**:
  If F is extensive and continuous at λ, then Γ_λ is a fixpoint.
-/
theorem continuous_implies_fixpoint_at_limit
    (F : Set PropT → Set PropT)
    (A0 : Set PropT)
    (hExt : ∀ Γ, Γ ⊆ F Γ)
    (limOrd : Ordinal)
    (hLim : Order.IsSuccLimit limOrd)
    -- Continuity hypothesis
    (hCont : F (transIter F A0 limOrd) = transUnion (fun β' => F (transIter F A0 β')) limOrd) :
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
    (hPC : ProvClosedDirectedOrd.{v} Provable)
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
    (hPCord : ProvClosedDirectedOrd.{u} Provable) -- Ordinal version
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{u})
    (hLim : Order.IsSuccLimit lim)
    -- Hyp 1: Absorption at some predecessor
    (hAbs : ∃ β < lim, Absorbable Provable (transIter (F Provable K Machine encode_halt Cn) A0.Γ (β + 1)))
    -- Hyp 2: Route II at limit
    (hRoute : RouteIIApplies Provable K Machine encode_halt Cn
              (transIter (F Provable K Machine encode_halt Cn) A0.Γ lim))
    -- Hyp 3: Continuity
    (hCont : F Provable K Machine encode_halt Cn (transIter (F Provable K Machine encode_halt Cn) A0.Γ lim) =
             transUnion (fun β' => F Provable K Machine encode_halt Cn
               (transIter (F Provable K Machine encode_halt Cn) A0.Γ β')) lim) :
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

end RevHalt
