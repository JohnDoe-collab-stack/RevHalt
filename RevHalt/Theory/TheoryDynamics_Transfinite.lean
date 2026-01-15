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
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro α hle
    rw [nonpos_iff_eq_zero] at hle
    subst hle
    exact le_refl _
  | succ γ ih =>
    intro α hle
    -- Goal is: transIter α ⊆ transIter (Order.succ γ)
    -- Order.succ γ = γ + 1, and transIter(γ+1) = F(transIter γ)
    have hsucc_eq : Order.succ γ = γ + 1 := Ordinal.add_one_eq_succ γ |>.symm
    rw [hsucc_eq, transIter_succ]
    -- Now goal is: transIter α ⊆ F(transIter γ)
    -- hle : α ≤ Order.succ γ
    by_cases h : α = Order.succ γ
    · -- α = Order.succ γ = γ + 1
      subst h
      rw [hsucc_eq, transIter_succ]
    · -- α < Order.succ γ, so α ≤ γ
      have hlt : α < Order.succ γ := lt_of_le_of_ne hle h
      have h_le_γ : α ≤ γ := Order.lt_succ_iff.mp hlt
      have h_sub_γ : transIter F A0 α ⊆ transIter F A0 γ := ih h_le_γ
      exact subset_trans h_sub_γ (hExt (transIter F A0 γ))
  | limit lim hLim ih =>
    intro α hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · rw [transIter_limit F A0 lim hLim]
      intro p hp
      exact ⟨α, hlt, hp⟩
    · exact Subset.rfl

end TransfiniteDynamics

section TransfiniteTheorems

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
    (hCnExt : CnExtensive Cn) -- For F extensivity
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCdir : ProvClosedDirected Provable)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal)
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
  -- Verify F is extensive: Γ ⊆ F(Γ)
  have hFExt : ∀ Γ, Γ ⊆ F_dyn Γ := fun Γ =>
    (subset_trans Set.subset_union_left (hCnExt _))

  have hFix : F_dyn (transIter F_dyn A0.Γ lim) = transIter F_dyn A0.Γ lim :=
    continuous_implies_fixpoint_at_limit F_dyn A0.Γ hFExt lim hLim hCont

  -- 2. Fixpoint => Admissibility
  let Γ_lim := transIter F_dyn A0.Γ lim
  let S_lim := S1Rel Provable K Machine encode_halt Γ_lim

  -- Geometric/Algebraic derivation of Cn-closed
  have hFix_symm : Γ_lim = Cn (Γ_lim ∪ S_lim) := by
    symm; simpa [F_dyn, F, S_lim] using hFix

  have hCnClosed : Cn Γ_lim = Γ_lim := by
    -- Step 1: Cn Γ = Cn (Cn ...)
    have hStep1 : Cn Γ_lim = Cn (Cn (Γ_lim ∪ S_lim)) :=
      congrArg Cn hFix_symm
    -- Step 2: Cn (Cn ...) = Cn (...)
    have hStep2 : Cn (Cn (Γ_lim ∪ S_lim)) = Cn (Γ_lim ∪ S_lim) :=
      hIdem (Γ_lim ∪ S_lim)
    -- Step 3: Cn (...) = Γ
    have hStep3 : Cn (Γ_lim ∪ S_lim) = Γ_lim :=
      hFix_symm.symm
    -- Combine
    rw [hStep1, hStep2, hStep3]

  -- ProvClosed (tricky part: Limit of successors).
  -- A0 is ProvClosed.
  -- Successors are F(Γ) = Cn(...), so ProvClosed (by hProvCn).
  -- Limit is Union of ProvClosed sets.
  -- By ProvClosedDirected (hPCdir).
  -- Need to show chain is directed and members are ProvClosed.
  have hChain : ∀ β < lim, ProvClosed Provable (transIter F_dyn A0.Γ β) := by
    -- Induction up to lim?
    -- Actually limitRecOn again or induction.
    intro β hlt
    induction β using Ordinal.limitRecOn with
    | zero =>
      simp; exact A0.prov_closed
    | succ γ ih =>
      -- Order.succ γ = γ + 1 for Ordinal
      show ProvClosed Provable (transIter F_dyn A0.Γ (γ + 1))
      rw [transIter_succ]
      -- F_dyn returns Cn(...), which is ProvClosed by hProvCn
      apply hProvCn
    | limit limOrd' hL ih =>
      rw [transIter_limit F_dyn A0.Γ limOrd' hL]
      -- ProvClosed for transfinite limits requires ProvClosedDirectedOrd hypothesis
      -- This is a known gap: ProvClosedDirected is for ℕ-indexed chains, not Ordinal
      -- Using sorry as a placeholder until ProvClosedDirectedOrd is added
      sorry -- ProvClosed for transfinite limit ordinals

  -- Combine for Admissibility
  -- Note: OmegaAdmissible requires ProvClosed for Γ_lim itself, not just for β < lim.
  -- This requires ProvClosedDirectedOrd (generalization of ProvClosedDirected to Ordinal).
  have hProvClosed_lim : ProvClosed Provable Γ_lim := by
    -- Γ_lim = transIter F_dyn A0.Γ lim is a transfinite union of ProvClosed sets
    -- Under ProvClosedDirectedOrd, this would be ProvClosed
    sorry -- Requires ProvClosedDirectedOrd: transfinite union of ProvClosed is ProvClosed
  have hAdm : OmegaAdmissible Provable Cn Γ_lim := ⟨hCnClosed, hProvClosed_lim⟩

  -- 3. Admissibility => S1 ≠ ∅
  have hNonEmpty : S1Rel Provable K Machine encode_halt Γ_lim ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp (hRoute hAdm)

  -- 4. Absorption => S1 = ∅
  -- Need FrontierInjected for the corrected limit_collapse_schema
  have hInj : FrontierInjected Provable K Machine encode_halt F_dyn :=
    frontierInjected_of_CnExt Provable K Machine encode_halt Cn hCnExt
  have hEmpty : S1Rel Provable K Machine encode_halt Γ_lim = ∅ :=
    limit_collapse_schema Provable K Machine encode_halt F_dyn A0.Γ hMono hFExt hInj lim hLim hAbs

  contradiction

end RevHalt
