import RevHalt.Base
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.Canonicity

T1: Canonicity of computational truth.

## Main Results
- `T1_traces`: Rev0_K captures exactly standard halting
- `T1_uniqueness`: Any two valid Kits yield the same verdict
- Semantic bridge definitions and `T1_semantics`
-/

namespace RevHalt

-- ==============================================================================================
-- T1: Canonicity of Rev
-- ==============================================================================================

/--
  **Theorem T1 (Traces)**:
  Under the assumption that K detects monotone properties, `Rev0_K` is extensionally equivalent
  to standard Halting for *all* traces (even non-monotone ones).
-/
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T := by
  intro T
  unfold Rev0_K Rev_K
  -- 1. Apply DetectsMonotone to the trace (up T), which is monotone.
  have h_mono : Monotone (up T) := up_mono T
  have h_equiv := hK (up T) h_mono
  rw [h_equiv]
  -- 2. Use the fact that ∃ n, up T n ↔ ∃ n, T n
  exact exists_up_iff T

/-- Corollary: Independence of the specific Kit. Any two valid Kits yield the same verdict. -/
theorem T1_uniqueness (K1 K2 : RHKit) (hK1 : DetectsMonotone K1) (hK2 : DetectsMonotone K2) :
    ∀ T, Rev0_K K1 T ↔ Rev0_K K2 T := by
  intro T
  rw [T1_traces K1 hK1, T1_traces K2 hK2]

-- -----------------------------------------------------------------------
-- Dynamic Bridge to Semantics
-- -----------------------------------------------------------------------

variable {Sentence : Type}
variable {Model : Type}
variable (Sat : Model → Sentence → Prop)

def ModE (Γ : Set Sentence) : Set Model := { M | ∀ φ ∈ Γ, Sat M φ }
def ThE (K_models : Set Model) : Set Sentence := { φ | ∀ M ∈ K_models, Sat M φ }
def CloE (Γ : Set Sentence) : Set Sentence := ThE Sat (ModE Sat Γ)
def SemConsequences (Γ : Set Sentence) (φ : Sentence) : Prop := φ ∈ CloE Sat Γ

variable (LR : Set Sentence → Sentence → Trace)

/-- The verdict of the Kit on a semantic pair (Γ, φ) via local reading. -/
def verdict_K (K : RHKit) (Γ : Set Sentence) (φ : Sentence) : Prop :=
  Rev0_K K (LR Γ φ)

/--
  **DynamicBridge Hypothesis**:
  Asserts that the specific Local Reading (LR) chosen successfully maps semantic consequence
  to the halting of the generated trace.
-/
def DynamicBridge : Prop :=
  ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)

/--
  **Theorem T1 (Semantics)**:
  If the Kit is valid and the Bridge holds, then semantic consequence is equivalent
  to the Kit's verdict.
-/
theorem T1_semantics (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ := by
  intro Γ φ
  unfold verdict_K
  rw [hBridge Γ φ]
  rw [T1_traces K hK]

end RevHalt
