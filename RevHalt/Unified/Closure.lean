/-
  RevHalt.Unified.Closure

  Static semantics layer (CloE) + dynamic bridge to Rev + kinetic layer.

  Design notes (implementation-level):
  * `Set α` is definitionaly `α → Prop` in Lean.
  * This file avoids *set equality* theorems; it works pointwise via `∈` / `↔`.

  Contents:
  - Static semantics: ModE / ThE / CloE / SemConsequences
  - Dynamic bridge: LocalReading + DynamicBridge + verdict_K
  - DR0/DR1: consequence ↔ verdict, and kit-invariance
  - Kinetics: Stage / CloK / CloRev with pointwise equivalences
-/

import RevHalt.Unified.Core
import Mathlib.Data.Set.Basic

universe u v

namespace RevHalt_Unified

open Set

/-! ## Static semantics: CloE -/

section Semantics

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Models satisfying Γ (Γ is a predicate on sentences). -/
def ModE (Γ : Set Sentence) : Set Model :=
  { M | ∀ φ, φ ∈ Γ → Sat M φ }

/-- Sentences true in all models of K. -/
def ThE (K : Set Model) : Set Sentence :=
  { φ | ∀ M, M ∈ K → Sat M φ }

/-- Semantic closure CloE(Γ) := ThE(ModE(Γ)). -/
def CloE (Γ : Set Sentence) : Set Sentence :=
  ThE Sat (ModE Sat Γ)

/-- Semantic consequence: φ ∈ CloE Sat Γ. -/
def SemConsequences (Γ : Set Sentence) (φ : Sentence) : Prop :=
  φ ∈ CloE Sat Γ

end Semantics

/-! ## Dynamic bridge to Rev -/

section Bridge

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Local reading from (Γ, φ) into a trace. -/
abbrev LocalReading :=
  Set Sentence → Sentence → Trace

variable (LR : LocalReading (Sentence := Sentence))

/-- The kit verdict on the trace LR Γ φ. -/
def verdict_K (K : RHKit) (Γ : Set Sentence) (φ : Sentence) : Prop :=
  Rev0_K K (LR Γ φ)

/-- Bridge hypothesis: semantic consequence ↔ halting of LR Γ φ. -/
def DynamicBridge : Prop :=
  ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)

/-- DR0: semantic consequence ↔ kit verdict, assuming DetectsMonotone and DynamicBridge. -/
theorem DR0_semantic_iff_verdict
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge (Sat := Sat) (LR := LR)) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K (LR := LR) K Γ φ := by
  intro Γ φ
  have h1 : SemConsequences Sat Γ φ ↔ Halts (LR Γ φ) := hBridge Γ φ
  have h2 : Rev0_K K (LR Γ φ) ↔ Halts (LR Γ φ) := T1_traces K hK (LR Γ φ)
  exact h1.trans h2.symm

/-- DR1: verdict invariance across kits (pointwise on any local reading). -/
theorem DR1_verdict_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, verdict_K (LR := LR) K₁ Γ φ ↔ verdict_K (LR := LR) K₂ Γ φ := by
  intro Γ φ
  have hL : verdict_K (LR := LR) K₁ Γ φ ↔ Halts (LR Γ φ) := by
    simpa [verdict_K] using (T1_traces K₁ h₁ (LR Γ φ))
  have hR : verdict_K (LR := LR) K₂ Γ φ ↔ Halts (LR Γ φ) := by
    simpa [verdict_K] using (T1_traces K₂ h₂ (LR Γ φ))
  exact hL.trans hR.symm

end Bridge

/-! ## Kinetics: stages and kinetic closures -/

section Kinetics

variable {Sentence : Type u}

variable (LR : LocalReading (Sentence := Sentence))

/-- Stage at time `t`: the set of sentences whose trace is true at time t. -/
def Stage (Γ : Set Sentence) (t : ℕ) : Set Sentence :=
  { φ | LR Γ φ t }

/-- Kinetic closure (limit): sentences whose trace is true at some time (i.e. Halts). -/
def CloK (Γ : Set Sentence) : Set Sentence :=
  { φ | Halts (LR Γ φ) }

/-- Robust kinetic closure: same closure but via a kit verdict (Rev0_K). -/
def CloRev (K : RHKit) (Γ : Set Sentence) : Set Sentence :=
  { φ | Rev0_K K (LR Γ φ) }

/-! ### Pointwise membership lemmas (no set equalities) -/

@[simp] theorem mem_Stage_iff (Γ : Set Sentence) (t : ℕ) (φ : Sentence) :
    φ ∈ Stage (LR := LR) Γ t ↔ LR Γ φ t := Iff.rfl

@[simp] theorem mem_CloK_iff (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloK (LR := LR) Γ ↔ Halts (LR Γ φ) := Iff.rfl

@[simp] theorem mem_CloK_iff_exists_time (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloK (LR := LR) Γ ↔ ∃ t, LR Γ φ t := by
  rfl

@[simp] theorem mem_CloRev_iff (K : RHKit) (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloRev (LR := LR) K Γ ↔ Rev0_K K (LR Γ φ) := Iff.rfl

/-- CloRev ↔ CloK pointwise, assuming DetectsMonotone (T1 on traces). -/
theorem CloRev_mem_iff_CloK_mem
    (K : RHKit) (hK : DetectsMonotone K) :
    ∀ Γ φ, (φ ∈ CloRev (LR := LR) K Γ) ↔ (φ ∈ CloK (LR := LR) Γ) := by
  intro Γ φ
  -- Rev0_K K (LR Γ φ) ↔ Halts (LR Γ φ)
  have h : Rev0_K K (LR Γ φ) ↔ Halts (LR Γ φ) := T1_traces K hK (LR Γ φ)
  -- unfold membership
  simpa [CloRev, CloK] using h

/-- Kit-invariance for CloRev, pointwise (immediate from DR1-style reasoning). -/
theorem CloRev_mem_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, (φ ∈ CloRev (LR := LR) K₁ Γ) ↔ (φ ∈ CloRev (LR := LR) K₂ Γ) := by
  intro Γ φ
  have hL : φ ∈ CloRev (LR := LR) K₁ Γ ↔ Halts (LR Γ φ) := by
    -- membership is definitional; reduce via T1_traces
    simpa [CloRev] using (T1_traces K₁ h₁ (LR Γ φ))
  have hR : φ ∈ CloRev (LR := LR) K₂ Γ ↔ Halts (LR Γ φ) := by
    simpa [CloRev] using (T1_traces K₂ h₂ (LR Γ φ))
  exact hL.trans hR.symm

end Kinetics

/-! ## DR0/DR1 expressed as membership in a (robust) kinetic closure -/

section DR_as_Closure

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

variable (LR : LocalReading (Sentence := Sentence))

/-- DynamicBridge restated: semantic consequence ↔ membership in CloK. -/
theorem Bridge_semantic_iff_CloK_mem
    (hBridge : (∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ))) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ (φ ∈ CloK (LR := LR) Γ) := by
  intro Γ φ
  -- RHS is definitional: φ ∈ {ψ | Halts (LR Γ ψ)}
  simpa [CloK] using (hBridge Γ φ)

/-- DR0 restated: semantic consequence ↔ membership in CloRev (kit verdict closure). -/
theorem DR0_semantic_iff_CloRev_mem
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : (∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ))) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ (φ ∈ CloRev (LR := LR) K Γ) := by
  intro Γ φ
  have h1 : SemConsequences Sat Γ φ ↔ Halts (LR Γ φ) := hBridge Γ φ
  have h2 : Rev0_K K (LR Γ φ) ↔ Halts (LR Γ φ) := T1_traces K hK (LR Γ φ)
  -- membership in CloRev is definitional
  -- Sem ↔ Halts ↔ Rev0
  exact h1.trans h2.symm

/-- DR1 restated: CloRev-membership does not depend on which kit is chosen (if both are valid). -/
theorem DR1_CloRev_mem_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, (φ ∈ CloRev (LR := LR) K₁ Γ) ↔ (φ ∈ CloRev (LR := LR) K₂ Γ) := by
  intro Γ φ
  -- both sides reduce to Halts via T1_traces
  have hL : φ ∈ CloRev (LR := LR) K₁ Γ ↔ Halts (LR Γ φ) := by
    simpa [CloRev] using (T1_traces K₁ h₁ (LR Γ φ))
  have hR : φ ∈ CloRev (LR := LR) K₂ Γ ↔ Halts (LR Γ φ) := by
    simpa [CloRev] using (T1_traces K₂ h₂ (LR Γ φ))
  exact hL.trans hR.symm

end DR_as_Closure

end RevHalt_Unified
