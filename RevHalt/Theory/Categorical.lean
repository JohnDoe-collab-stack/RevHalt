import RevHalt.Base.Trace
import RevHalt.Theory.Canonicity
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

/-!
# RevHalt.Theory.Categorical

Order- and category-theoretic structure already present in RevHalt:

1. `up` is the reflection of an arbitrary trace into the class of monotone traces:
   for monotone `X`, `up T ≤ X ↔ T ≤ X` (adjunction in a thin category / poset).

2. `ModE` / `ThE` form a Galois-style adjunction (thin category view),
   and `CloE = ThE ∘ ModE` is a closure operator (extensive, monotone, idempotent).
-/

namespace RevHalt

-- =====================================================================================
-- Pointwise order on traces
-- =====================================================================================

/-- Pointwise implication order on traces: `T ≤ U` means `∀ n, T n → U n`. -/
instance : LE Trace := ⟨fun T U => ∀ n : ℕ, T n → U n⟩

-- =====================================================================================
-- 1) `up` as a reflector / closure operator on traces (thin category view)
-- =====================================================================================

theorem le_up (T : Trace) : T ≤ up T := by
  intro n hn
  exact ⟨n, Nat.le_refl n, hn⟩

/-- `up` is monotone w.r.t. the pointwise order on traces. -/
theorem up_mono_order {T U : Trace} (h : T ≤ U) : up T ≤ up U := by
  intro n hn
  rcases hn with ⟨k, hk_le, hkT⟩
  exact ⟨k, hk_le, h k hkT⟩

/--
Reflection law: for monotone `X`, `up T ≤ X ↔ T ≤ X`.
-/
theorem up_le_iff {T X : Trace} (hX : Monotone X) :
    up T ≤ X ↔ T ≤ X := by
  constructor
  · intro hup n hn
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    exact hup n this
  · intro hTX n hn
    rcases hn with ⟨k, hk_le, hkT⟩
    have hXk : X k := hTX k hkT
    have hkn : X k → X n := hX hk_le
    exact hkn hXk

/-- `up (up T) ≤ up T`. -/
theorem up_idem_le (T : Trace) : up (up T) ≤ up T := by
  intro n hn
  rcases hn with ⟨k, hk_le, hk_up⟩
  rcases hk_up with ⟨j, hj_le, hjT⟩
  exact ⟨j, Nat.le_trans hj_le hk_le, hjT⟩

/-- `up T ≤ up (up T)`. -/
theorem le_up_idem (T : Trace) : up T ≤ up (up T) := by
  intro n hn
  rcases hn with ⟨k, hk_le, hkT⟩
  have : up T k := ⟨k, Nat.le_refl k, hkT⟩
  exact ⟨k, hk_le, this⟩

/-- Idempotence as equality of traces. -/
theorem up_idem (T : Trace) : up (up T) = up T := by
  funext n
  apply propext
  constructor
  · exact (up_idem_le (T := T)) n
  · exact (le_up_idem (T := T)) n


-- =====================================================================================
-- 2) `ModE` / `ThE` / `CloE` as Galois-style structure; `CloE` is a closure operator
-- =====================================================================================

section Semantics

variable {Sentence : Type}
variable {Model : Type}
variable (Sat : Model → Sentence → Prop)

theorem ModE_ThE_iff (Γ : Set Sentence) (K_models : Set Model) :
    K_models ⊆ ModE Sat Γ ↔ Γ ⊆ ThE Sat K_models := by
  constructor
  · intro hKM φ hφ M hM
    have hM' : M ∈ ModE Sat Γ := hKM hM
    exact hM' φ hφ
  · intro hΓ M hM φ hφ
    have hφ' : φ ∈ ThE Sat K_models := hΓ hφ
    exact hφ' M hM

theorem subset_CloE (Γ : Set Sentence) : Γ ⊆ CloE Sat Γ := by
  intro φ hφ M hM
  exact hM φ hφ

theorem CloE_monotone {Γ Δ : Set Sentence} (h : Γ ⊆ Δ) :
    CloE Sat Γ ⊆ CloE Sat Δ := by
  intro φ hφ M hMΔ
  have hMΓ : M ∈ ModE Sat Γ := by
    intro ψ hψ
    exact hMΔ ψ (h hψ)
  exact hφ M hMΓ

theorem ModE_CloE_eq (Γ : Set Sentence) :
    ModE Sat (CloE Sat Γ) = ModE Sat Γ := by
  ext M
  constructor
  · intro hMClo φ hφ
    have : φ ∈ CloE Sat Γ := subset_CloE (Sat := Sat) Γ hφ
    exact hMClo φ this
  · intro hMΓ φ hφ
    exact hφ M hMΓ

theorem CloE_idem (Γ : Set Sentence) :
    CloE Sat (CloE Sat Γ) = CloE Sat Γ := by
  have h : ModE Sat (CloE Sat Γ) = ModE Sat Γ := ModE_CloE_eq (Sat := Sat) Γ
  show ThE Sat (ModE Sat (CloE Sat Γ)) = CloE Sat Γ
  rw [h]
  rfl

end Semantics

end RevHalt
