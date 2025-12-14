import RevHalt.Theory
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Kinetic.Closure

Static semantics layer (CloE) + dynamic bridge to Rev + kinetic layer.

## Contents
- Stage / CloK / CloRev with pointwise equivalences
- DR0/DR1: consequence ↔ verdict, and kit-invariance
-/

namespace RevHalt

open Set

/-! ## Kinetics: stages and kinetic closures -/

variable {Sentence : Type}

/-- Local reading from (Γ, φ) into a trace. -/
abbrev LocalReading (Sentence : Type) :=
  Set Sentence → Sentence → Trace

variable (LR : LocalReading Sentence)

/-- Stage at time `t`: the set of sentences whose trace is true at time t. -/
def Stage (Γ : Set Sentence) (t : ℕ) : Set Sentence :=
  { φ | LR Γ φ t }

/-- Kinetic closure (limit): sentences whose trace is true at some time (i.e. Halts). -/
def CloK (Γ : Set Sentence) : Set Sentence :=
  { φ | Halts (LR Γ φ) }

/-- Robust kinetic closure: same closure but via a kit verdict (Rev0_K). -/
def CloRev (K : RHKit) (Γ : Set Sentence) : Set Sentence :=
  { φ | Rev0_K K (LR Γ φ) }

/-! ### Pointwise membership lemmas -/

@[simp] theorem mem_Stage_iff (Γ : Set Sentence) (t : ℕ) (φ : Sentence) :
    φ ∈ Stage LR Γ t ↔ LR Γ φ t := Iff.rfl

@[simp] theorem mem_CloK_iff (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloK LR Γ ↔ Halts (LR Γ φ) := Iff.rfl

@[simp] theorem mem_CloK_iff_exists_time (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloK LR Γ ↔ ∃ t, LR Γ φ t := by
  rfl

@[simp] theorem mem_CloRev_iff (K : RHKit) (Γ : Set Sentence) (φ : Sentence) :
    φ ∈ CloRev LR K Γ ↔ Rev0_K K (LR Γ φ) := Iff.rfl

/-- CloRev ↔ CloK pointwise, assuming DetectsMonotone (T1 on traces). -/
theorem CloRev_mem_iff_CloK_mem
    (K : RHKit) (hK : DetectsMonotone K) :
    ∀ Γ φ, (φ ∈ CloRev LR K Γ) ↔ (φ ∈ CloK LR Γ) := by
  intro Γ φ
  have h : Rev0_K K (LR Γ φ) ↔ Halts (LR Γ φ) := T1_traces K hK (LR Γ φ)
  simpa [CloRev, CloK] using h

/-- Kit-invariance for CloRev, pointwise. -/
theorem CloRev_mem_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, (φ ∈ CloRev LR K₁ Γ) ↔ (φ ∈ CloRev LR K₂ Γ) := by
  intro Γ φ
  have hL : φ ∈ CloRev LR K₁ Γ ↔ Halts (LR Γ φ) := by
    simpa [CloRev] using (T1_traces K₁ h₁ (LR Γ φ))
  have hR : φ ∈ CloRev LR K₂ Γ ↔ Halts (LR Γ φ) := by
    simpa [CloRev] using (T1_traces K₂ h₂ (LR Γ φ))
  exact hL.trans hR.symm

end RevHalt
