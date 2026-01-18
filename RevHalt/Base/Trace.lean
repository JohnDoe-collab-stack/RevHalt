import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

/-!
# RevHalt.Base.Trace

Foundational definitions for traces and halting (Axiom-Free Version).

## Contents
- `Trace` := ℕ → Prop
- `Halts` := ∃ n, T n
- `up` operator (cumulative monotonization)
- `Mono` predicate (constructive monotonicity)
- `up_mono`, `exists_up_iff` lemmas
-/

namespace RevHalt

/-- A Trace is a predicate on natural numbers (representing state at time n). -/
def Trace := ℕ → Prop

/-- Standard Halting definition: a trace halts if it eventually becomes true. -/
def Halts (T : Trace) : Prop := ∃ n, T n

/-- The "up" operator: converts any trace into a cumulative (monotone) trace. -/
def up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k

/--
  Constructive Monotonicity.
  Defined specifically for Traces to avoid Mathlib's class hierarchy and axioms.
-/
def TMono (T : Trace) : Prop :=
  ∀ ⦃n m⦄, n ≤ m → T n → T m

/--
  Foundational definition: UpFixed (Fixed Point of Closure).
  A trace is "closed" (or well-formed) if it is a fixed point of `up`.
  This is the structural definition of monotonicity in this framework.
-/
def UpFixed (T : Trace) : Prop :=
  ∀ n, up T n ↔ T n

/-- Helper: up(T) is always monotone. -/
lemma up_mono (T : Trace) : TMono (up T) := by
  intro n m hnm h
  obtain ⟨k, hk_le_n, hk_T⟩ := h
  -- if k ≤ n and n ≤ m, then k ≤ m
  exact ⟨k, Nat.le_trans hk_le_n hnm, hk_T⟩

/-- Helper: up(T) is always a fixed point. -/
lemma up_fixed (T : Trace) : UpFixed (up T) := by
  intro n
  constructor
  · intro h
    -- up (up T) n -> exists k <= n, up T k
    obtain ⟨k, hk_le, ⟨j, hj_le, hj_T⟩⟩ := h
    -- j <= k <= n -> j <= n
    exact ⟨j, Nat.le_trans hj_le hk_le, hj_T⟩
  · intro h
    -- up T n -> up (up T) n (trivial direction)
    exact ⟨n, Nat.le_refl n, h⟩

/-- Equivalence: Dynamic Monotonicity implies Structural Fixed Point. -/
lemma TMono_to_UpFixed (T : Trace) (h : TMono T) : UpFixed T := by
  intro n
  constructor
  · intro hup
    obtain ⟨k, hk_le, hk_T⟩ := hup
    exact h hk_le hk_T
  · intro hn
    exact ⟨n, Nat.le_refl n, hn⟩

/-- Equivalence: Structural Fixed Point implies Dynamic Monotonicity. -/
lemma UpFixed_to_TMono (T : Trace) (hfix : UpFixed T) : TMono T := by
  intro n m hnm hn
  -- want T m
  -- use fixpoint: T m ↔ up T m
  have : up T m := by
    -- build up T m from witness n
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    -- transport up T n to up T m using monotonicity of up (already have up_mono)
    exact up_mono T hnm this
  exact (hfix m).1 this

/-- Helper: Halting is preserved by up. -/
lemma exists_up_iff (T : Trace) : (∃ n, up T n) ↔ (∃ n, T n) := by
  constructor
  · intro h
    obtain ⟨n, k, hk_le_n, hk_T⟩ := h
    exact ⟨k, hk_T⟩
  · intro h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, n, Nat.le_refl n, hn⟩

/-- Bottom trace (⊥): always false. -/
def bottom : Trace := fun _ => False

notation "⊥ₜ" => bottom

/--
  Axiom-free version of "up T = ⊥".
  Instead of equality (which requires propext/funext), we use pointwise equivalence.
-/
lemma up_iff_bottom_iff_forall_not (T : Trace) :
    (∀ n, up T n ↔ (⊥ₜ) n) ↔ ∀ n, ¬ T n := by
  constructor
  · intro h n hn
    -- up T n is equivalent to False, so it implies False
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    have : (⊥ₜ) n := (h n).1 this
    exact False.elim this
  · intro h n
    constructor
    · intro hup
      obtain ⟨k, hk, hkT⟩ := hup
      exact (h k) hkT
    · intro hbot
      exact False.elim hbot

/-- Just the implication direction (often more useful/natural). -/
lemma forall_not_up_iff_forall_not (T : Trace) :
    (∀ n, ¬ up T n) ↔ (∀ n, ¬ T n) := by
  constructor
  · intro h n hn
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    exact (h n) this
  · intro h n hup
    obtain ⟨k, hk, hkT⟩ := hup
    exact (h k) hkT

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Trace
#print axioms RevHalt.Halts
#print axioms RevHalt.up
#print axioms RevHalt.TMono
#print axioms RevHalt.UpFixed
#print axioms RevHalt.up_mono
#print axioms RevHalt.up_fixed
#print axioms RevHalt.TMono_to_UpFixed
#print axioms RevHalt.UpFixed_to_TMono
#print axioms RevHalt.exists_up_iff
#print axioms RevHalt.bottom
#print axioms RevHalt.up_iff_bottom_iff_forall_not
#print axioms RevHalt.forall_not_up_iff_forall_not
