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
  Under the assumption that K detects *closed* (fixed-point) properties, `Rev0_K` is extensionally equivalent
  to standard Halting for *all* traces (even non-closed ones).
-/
theorem T1_traces (K : RHKit) (hK : DetectsUpFixed K) :
    ∀ T : Trace, Rev0_K K T ↔ Halts T := by
  intro T
  -- 1. Apply DetectsUpFixed to the trace (up T), which is closed (fixed point).
  have h_fix : UpFixed (up T) := up_fixed T
  -- h_equiv : K.Proj (up T) ↔ ∃ n, up T n
  have h_equiv := hK (up T) h_fix
  -- 2. Use the fact that ∃ n, up T n ↔ ∃ n, T n
  have h_ex := exists_up_iff T
  -- Rev0_K K T is definitionally K.Proj (up T)
  -- So we just transitivity chain them: Rev0_K K T ↔ ∃ n, up T n ↔ hal T
  exact h_equiv.trans h_ex

/--
  **Corollary (Stabilization)**:
  The negative verdict of a valid Kit captures exactly the stabilization property (never halting).
  `¬ Rev0_K K T ↔ ∀ n, ¬ T n` (classically equivalent to ¬Halts, constructively defined as Stabilizes).
-/
theorem T1_neg_traces (K : RHKit) (hK : DetectsUpFixed K) :
    ∀ T : Trace, ¬ Rev0_K K T ↔ ¬ Halts T := by
  intro T
  -- Direct negation congruence to avoid propext from rw
  exact not_congr (T1_traces K hK T)

/-- Corollary: Independence of the specific Kit. Any two valid Kits yield the same verdict. -/
theorem T1_uniqueness (K1 K2 : RHKit) (hK1 : DetectsUpFixed K1) (hK2 : DetectsUpFixed K2) :
    ∀ T : Trace, Rev0_K K1 T ↔ Rev0_K K2 T := by
  intro T
  -- Transitivity via Halts T: Rev K1 T ↔ Halts T ↔ Rev K2 T
  exact (T1_traces K1 hK1 T).trans (T1_traces K2 hK2 T).symm

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

/-- Simp lemma: membership in ModE. -/
@[simp] lemma mem_ModE (Γ : Set Sentence) (M : Model) :
    M ∈ ModE Sat Γ ↔ ∀ φ ∈ Γ, Sat M φ := Iff.rfl

/-- Simp lemma: membership in ThE. -/
@[simp] lemma mem_ThE (K_models : Set Model) (φ : Sentence) :
    φ ∈ ThE Sat K_models ↔ ∀ M ∈ K_models, Sat M φ := Iff.rfl

/-- Simp lemma: SemConsequences unfolding. -/
@[simp] lemma SemConsequences_iff (Γ : Set Sentence) (φ : Sentence) :
    SemConsequences Sat Γ φ ↔ φ ∈ CloE Sat Γ := Iff.rfl

/-- Simp lemma: CloE definition. -/
lemma CloE_eq (Γ : Set Sentence) :
    CloE Sat Γ = ThE Sat (ModE Sat Γ) := rfl

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
theorem T1_semantics (K : RHKit) (hK : DetectsUpFixed K)
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ := by
  intro Γ φ
  -- verdict_K is Rev0_K ...
  -- hBridge : Sem ... ↔ Halts ...
  -- T1_traces : Rev0_K ... ↔ Halts ...
  -- Goal: Sem ... ↔ Rev0_K ...
  -- Sem ↔ Halts ↔ Rev0_K
  exact (hBridge Γ φ).trans (T1_traces K hK (LR Γ φ)).symm

end RevHalt

-- Axiom checks:
#print axioms RevHalt.T1_traces
#print axioms RevHalt.T1_neg_traces
#print axioms RevHalt.T1_uniqueness
#print axioms RevHalt.mem_ModE
#print axioms RevHalt.mem_ThE
#print axioms RevHalt.SemConsequences_iff
#print axioms RevHalt.CloE_eq
#print axioms RevHalt.T1_semantics
