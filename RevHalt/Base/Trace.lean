import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic

/-!
# RevHalt.Base.Trace

Foundational definitions for traces and halting.

## Contents
- `Trace` := ℕ → Prop
- `Halts` := ∃ n, T n
- `up` operator (cumulative monotonization)
- `up_mono`, `exists_up_iff` lemmas
-/

namespace RevHalt

/-- A Trace is a predicate on natural numbers (representing state at time n). -/
def Trace := ℕ → Prop

/-- Standard Halting definition: a trace halts if it eventually becomes true. -/
def Halts (T : Trace) : Prop := ∃ n, T n

/-- The "up" operator: converts any trace into a cumulative (monotone) trace. -/
def up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k

/-- Helper: up(T) is always monotone. -/
lemma up_mono (T : Trace) : Monotone (up T) := by
  intro n m hnm h
  obtain ⟨k, hk_le_n, hk_T⟩ := h
  use k
  constructor
  · exact Nat.le_trans hk_le_n hnm
  · exact hk_T

/-- Helper: Halting is preserved by up. -/
lemma exists_up_iff (T : Trace) : (∃ n, up T n) ↔ (∃ n, T n) := by
  constructor
  · intro h
    obtain ⟨n, k, hk_le_n, hk_T⟩ := h
    use k, hk_T
  · intro h
    obtain ⟨n, hn⟩ := h
    use n, n, Nat.le_refl n, hn

end RevHalt
