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
-- 1.5) Stabilization as Partial Order Bottom
-- =====================================================================================

/-- The bottom trace (constantly false). -/
def BotTrace : Trace := fun _ => False

instance : Bot Trace := ⟨BotTrace⟩

@[simp] lemma bot_trace_apply (n : ℕ) : (⊥ : Trace) n = False := rfl

/-- `up` preserves bottom. -/
theorem up_bot : up ⊥ = ⊥ := by
  funext n
  apply propext
  constructor
  · intro h
    rcases h with ⟨k, _, hk⟩
    exact hk
  · intro h
    exact False.elim h

/--
  **Algebraic Stabilization (The Operative Core)**:
  Standard theory defines stabilization logically (`∀ n, ¬ T n`).
  RevHalt defines it operatively via the `up` closure (`up T = ⊥`).

  The novelty is the operator `up` itself: it acts as a **Projector** / **Filter**.
  - If `T` contains any signal (Halt), `up T` imposes `True` (eventually).
  - If `T` stabilizes (No Halt), `up T` collapses to `⊥`.

  This makes Stabilization a **structural nullity** detected by the operator,
  rather than just a logical negation.
-/
theorem up_eq_bot_iff (T : Trace) :
    up T = ⊥ ↔ ∀ n, ¬ T n := by
  constructor
  · intro h n hn
    have hT : T ≤ up T := le_up T
    have hBot : up T n := hT n hn
    rw [h] at hBot
    exact hBot
  · intro h
    funext n
    apply propext
    constructor
    · intro hUp
      rcases hUp with ⟨k, _, hk⟩
      exact h k hk
    · intro hBot
      exact False.elim hBot

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


-- =====================================================================================
-- 1.6) Operative Projector Proofs (The "Filter" Demonstration)
-- =====================================================================================

/--
  **Theorem: `up` is a Projector/Filter**.
  This theorem bundles the three properties that demonstrate the operative nature:
  1. **Idempotence**: Applying it twice changes nothing (Projector).
  2. **Signal Preservation**: If there is a signal (Halts), it survives.
  3. **Noise Annihilation**: If there is no signal (Stabilizes), it collapses to Bot.
-/
theorem up_is_projector (T : Trace) :
    (up (up T) = up T) ∧                  -- Idempotence
    ((∃ n, up T n) ↔ (∃ n, T n)) ∧        -- Signal Preservation
    (up T = ⊥ ↔ ∀ n, ¬ T n) :=            -- Noise Annihilation (Kernel)
by
  refine ⟨?_, ?_, ?_⟩
  · exact up_idem T
  · exact exists_up_iff T
  · exact up_eq_bot_iff T

end RevHalt
