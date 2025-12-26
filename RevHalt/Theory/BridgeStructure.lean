import RevHalt.Base
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Categorical
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.BridgeStructure

Structural conditions on `LR : Set Sentence → Sentence → Trace`.

`LR` is a "compiler" from the semantic world (theories with closure `CloE`)
to the dynamic world (traces with closure `up`). These conditions express
whether `LR` respects this geometry.

## Contents

1. `LR_depends_only_on_CloE` — invariance under semantic equivalence
2. `LR_closed_invariant` — Γ and CloE Γ produce the same trace
3. `LR_mono_Γ` — monotonicity in axiom sets
4. `LR_commutes_with_closure` — central: up ∘ LR = LR ∘ CloE

## Main Results

- `verdict_via_closed_theory`: with commutation, verdict depends only on CloE Γ
- `bridge_reduces_to_closed`: DynamicBridge need only be checked on closed theories
-/

namespace RevHalt

variable {Sentence Model : Type}
variable (Sat : Model → Sentence → Prop)
variable (LR : Set Sentence → Sentence → Trace)

-- =====================================================================================
-- 1) Invariance under Closure (no syntactic parasitism)
-- =====================================================================================

/-- Strong: LR depends only on semantic content (CloE), not on presentation. -/
def LR_depends_only_on_CloE : Prop :=
  ∀ Γ Δ φ, CloE Sat Γ = CloE Sat Δ → LR Γ φ = LR Δ φ

/-- Minimal: closing Γ does not change the trace. -/
def LR_closed_invariant : Prop :=
  ∀ Γ φ, LR (CloE Sat Γ) φ = LR Γ φ

theorem closed_invariant_of_depends_only (h : LR_depends_only_on_CloE Sat LR) :
    LR_closed_invariant Sat LR := by
  intro Γ φ
  exact h (CloE Sat Γ) Γ φ (CloE_idem (Sat := Sat) Γ)

-- =====================================================================================
-- 2) Monotonicity in Γ (functoriality)
-- =====================================================================================

/-- Adding axioms does not make the trace "less true" over time. -/
def LR_mono_Γ : Prop :=
  ∀ {Γ Δ : Set Sentence} (φ : Sentence), Γ ⊆ Δ → LR Γ φ ≤ LR Δ φ

-- =====================================================================================
-- 3) Central Condition: Commutation of Closures
-- =====================================================================================

/-- The operational normalization `up` matches semantic closure `CloE`. -/
def LR_commutes_with_closure : Prop :=
  ∀ Γ φ, up (LR Γ φ) = LR (CloE Sat Γ) φ

/-- If closures commute, then LR is also closed-invariant (up to `up`). -/
theorem closed_invariant_up_of_commutes (h : LR_commutes_with_closure Sat LR) :
    ∀ Γ φ, up (LR (CloE Sat Γ) φ) = up (LR Γ φ) := by
  intro Γ φ
  rw [h (CloE Sat Γ) φ, h Γ φ, CloE_idem (Sat := Sat) Γ]

-- =====================================================================================
-- 4) Transport Theorems: Impact on Verdict
-- =====================================================================================

/-- With commutation, the verdict depends only on the closed theory. -/
theorem verdict_via_closed_theory (K : RHKit)
    (h : LR_commutes_with_closure Sat LR) :
    ∀ Γ φ, Rev0_K K (LR Γ φ) = K.Proj (LR (CloE Sat Γ) φ) := by
  intro Γ φ
  unfold Rev0_K Rev_K
  rw [h Γ φ]

/-- Theories with the same closure give the same verdict. -/
theorem verdict_eq_of_CloE_eq (K : RHKit)
    (hDep : LR_depends_only_on_CloE Sat LR) :
    ∀ Γ Δ φ, CloE Sat Γ = CloE Sat Δ → (Rev0_K K (LR Γ φ) ↔ Rev0_K K (LR Δ φ)) := by
  intro Γ Δ φ hEq
  rw [hDep Γ Δ φ hEq]

-- =====================================================================================
-- 5) Reduction of DynamicBridge to Closed Theories
-- =====================================================================================

/-- DynamicBridge restricted to closed theories. -/
def DynamicBridgeClosed : Prop :=
  ∀ Γ φ, CloE Sat Γ = Γ → (SemConsequences Sat Γ φ ↔ Halts (LR Γ φ))

/-- If LR is closed-invariant, then DynamicBridge on all theories reduces to closed ones. -/
theorem bridge_reduces_to_closed
    (hInv : LR_closed_invariant Sat LR)
    (hBridgeClosed : DynamicBridgeClosed Sat LR) :
    DynamicBridge Sat LR := by
  intro Γ φ
  -- SemConsequences Sat Γ φ = φ ∈ CloE Sat Γ
  -- Use the fact that CloE (CloE Γ) = CloE Γ
  have hClosed : CloE Sat (CloE Sat Γ) = CloE Sat Γ := CloE_idem (Sat := Sat) Γ
  have hBridge := hBridgeClosed (CloE Sat Γ) φ hClosed
  -- SemConsequences Sat Γ φ = SemConsequences Sat (CloE Sat Γ) φ
  have hSemEq : SemConsequences Sat Γ φ ↔ SemConsequences Sat (CloE Sat Γ) φ := by
    unfold SemConsequences
    constructor
    · intro h
      rw [hClosed]
      exact h
    · intro h
      rw [← hClosed]
      exact h
  rw [hSemEq, hBridge]
  -- Halts (LR (CloE Sat Γ) φ) ↔ Halts (LR Γ φ) by hInv
  rw [hInv Γ φ]

end RevHalt
