import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Encodable.Basic

/-!
# AbstractDynamics

Navigation dynamics derived from the StructuralDichotomy schema.

## Key Point

The dynamics is **independent of Trace/up**. It depends only on:
- A type of "codes" (Index)
- A type of "propositions" (PropT)
- A truth predicate (Truth : PropT → Prop)
- A pick function (pick : Index → PropT) with truth proof

The schedule-invariance, soundness preservation, omegaState minimality —
all derived abstractly, instantiated for free.

## The Problem That Couldn't Be Stated

"When is a dichotomy structural rather than extensional?"

Answer: when it instantiates StructuralDichotomy.

This file shows the dynamics that follows from any such instantiation.
-/

namespace RevHalt.AbstractDynamics

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Abstract Sound State
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A corpus S is sound w.r.t. Truth if all its members are true. -/
def Sound {PropT : Type} (Truth : PropT → Prop) (S : Set PropT) : Prop :=
  ∀ p, p ∈ S → Truth p

/-- Empty set is sound. -/
theorem sound_empty {PropT : Type} (Truth : PropT → Prop) :
    Sound Truth (∅ : Set PropT) := by
  intro p hp
  exact False.elim hp

/-- Adding a true element preserves soundness. -/
theorem sound_union_singleton {PropT : Type} (Truth : PropT → Prop)
    (S : Set PropT) (p : PropT)
    (hS : Sound Truth S) (hp : Truth p) :
    Sound Truth (S ∪ {p}) := by
  intro q hq
  cases hq with
  | inl hqS => exact hS q hqS
  | inr hqp => rw [hqp]; exact hp

/-- Sound is closed under arbitrary union. -/
theorem sound_iUnion {ι PropT : Type} (Truth : PropT → Prop) (S : ι → Set PropT)
    (h : ∀ i, Sound Truth (S i)) :
    Sound Truth (⋃ i, S i) := by
  intro p hp
  rw [Set.mem_iUnion] at hp
  obtain ⟨i, hi⟩ := hp
  exact h i p hi

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Abstract PickWorld
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A PickWorld: the minimal data for navigation dynamics.
- Index: type of "codes" to navigate
- PropT: type of "propositions"
- Truth: external truth predicate
- pick: for each code, the proposition to add
- pick_true: each pick is true

This is what remains of OraclePick after abstracting away Σ₁/Π₁ details.
-/
structure PickWorld (Index PropT : Type) where
  Truth : PropT → Prop
  pick : Index → PropT
  pick_true : ∀ i, Truth (pick i)

namespace PickWorld

variable {Index PropT : Type} (W : PickWorld Index PropT)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) State and Step
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A state is a corpus S with a proof of soundness. -/
structure State where
  S : Set PropT
  sound : Sound W.Truth S

/-- The initial (empty) state. -/
def State.empty : W.State where
  S := ∅
  sound := sound_empty W.Truth

/-- A single step: add pick i to the state. -/
def step (st : W.State) (i : Index) : W.State where
  S := st.S ∪ {W.pick i}
  sound := sound_union_singleton W.Truth st.S (W.pick i) st.sound (W.pick_true i)

/-- Step is monotone. -/
theorem step_mono (st : W.State) (i : Index) : st.S ⊆ (W.step st i).S := by
  intro p hp
  exact Or.inl hp

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Chain and Limit
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Chain: iteration of steps along a schedule. -/
def Chain (S0 : W.State) (schedule : ℕ → Index) : ℕ → W.State
  | 0 => S0
  | n + 1 => W.step (Chain S0 schedule n) (schedule n)

/-- Limit of a chain. -/
def lim (C : ℕ → Set PropT) : Set PropT := ⋃ n, C n

theorem mem_lim {C : ℕ → Set PropT} {p : PropT} :
    p ∈ lim C ↔ ∃ n, p ∈ C n := by
  unfold lim
  rw [Set.mem_iUnion]

/-- Chain monotonicity. -/
theorem chain_mono (S0 : W.State) (schedule : ℕ → Index) (n : ℕ) :
    (W.Chain S0 schedule n).S ⊆ (W.Chain S0 schedule (n + 1)).S := by
  exact W.step_mono (W.Chain S0 schedule n) (schedule n)

/-- All chain states are sound. -/
theorem chain_sound (S0 : W.State) (schedule : ℕ → Index) (n : ℕ) :
    Sound W.Truth (W.Chain S0 schedule n).S :=
  (W.Chain S0 schedule n).sound

/-- Limit of a sound chain is sound. -/
theorem lim_sound (S0 : W.State) (schedule : ℕ → Index) :
    Sound W.Truth (lim (fun n => (W.Chain S0 schedule n).S)) := by
  apply sound_iUnion
  intro n
  exact W.chain_sound S0 schedule n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Closed Form
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Prefix picks: picks from indices 0 to n-1. -/
def prefixPicks (schedule : ℕ → Index) (n : ℕ) : Set PropT :=
  { p | ∃ i, i < n ∧ p = W.pick (schedule i) }

/-- All picks (unbounded). -/
def allPicksUnbounded (schedule : ℕ → Index) : Set PropT :=
  { p | ∃ i, p = W.pick (schedule i) }

/-- Closed form of chain at step n. -/
theorem chain_closed_form (S0 : W.State) (schedule : ℕ → Index) (n : ℕ) :
    (W.Chain S0 schedule n).S = S0.S ∪ W.prefixPicks schedule n := by
  induction n with
  | zero =>
    unfold Chain prefixPicks
    ext p
    constructor
    · intro hp; exact Or.inl hp
    · intro hp
      cases hp with
      | inl h => exact h
      | inr h =>
        obtain ⟨i, hi, _⟩ := h
        exact False.elim (Nat.not_lt_zero i hi)
  | succ k ih =>
    unfold Chain step prefixPicks
    ext p
    constructor
    · intro hp
      cases hp with
      | inl h =>
        rw [ih] at h
        cases h with
        | inl hS0 => exact Or.inl hS0
        | inr hpre =>
          apply Or.inr
          obtain ⟨i, hi, hpeq⟩ := hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, hpeq⟩
      | inr h =>
        apply Or.inr
        exact ⟨k, Nat.lt_succ_self k, h⟩
    · intro hp
      cases hp with
      | inl hS0 =>
        apply Or.inl
        rw [ih]
        exact Or.inl hS0
      | inr hpre =>
        obtain ⟨i, hi, hpeq⟩ := hpre
        cases Nat.lt_succ_iff_lt_or_eq.mp hi with
        | inl hlt =>
          apply Or.inl
          rw [ih]
          exact Or.inr ⟨i, hlt, hpeq⟩
        | inr heq =>
          apply Or.inr
          rw [heq] at hpeq
          exact hpeq

/-- Closed form of limit. -/
theorem lim_closed_form (S0 : W.State) (schedule : ℕ → Index) :
    lim (fun n => (W.Chain S0 schedule n).S) = S0.S ∪ W.allPicksUnbounded schedule := by
  ext p
  constructor
  · intro hp
    rw [mem_lim] at hp
    obtain ⟨n, hn⟩ := hp
    rw [W.chain_closed_form] at hn
    cases hn with
    | inl hS0 => exact Or.inl hS0
    | inr hpre =>
      obtain ⟨i, _, hpeq⟩ := hpre
      exact Or.inr ⟨i, hpeq⟩
  · intro hp
    cases hp with
    | inl hS0 =>
      rw [mem_lim]
      exact ⟨0, hS0⟩
    | inr hall =>
      rw [mem_lim]
      obtain ⟨i, hpeq⟩ := hall
      use i + 1
      rw [W.chain_closed_form]
      exact Or.inr ⟨i, Nat.lt_succ_self i, hpeq⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Fair Schedule and Coverage
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A schedule is fair if every index appears at least once. -/
def Fair (schedule : ℕ → Index) : Prop :=
  ∀ i : Index, ∃ n : ℕ, schedule n = i

/-- All picks (independent of schedule). -/
def AllPicks : Set PropT := { p | ∃ i, p = W.pick i }

/-- Under a fair schedule, limit contains all picks. -/
theorem lim_contains_all_picks (S0 : W.State) (schedule : ℕ → Index) (hFair : Fair schedule) :
    W.AllPicks ⊆ lim (fun n => (W.Chain S0 schedule n).S) := by
  intro p hp
  obtain ⟨i, hpeq⟩ := hp
  obtain ⟨n, hn⟩ := hFair i
  rw [mem_lim]
  use n + 1
  rw [W.chain_closed_form]
  apply Or.inr
  exact ⟨n, Nat.lt_succ_self n, by rw [hn]; exact hpeq⟩

/-- Schedule-free characterization of limit. -/
theorem lim_schedule_free (S0 : W.State) (schedule : ℕ → Index) (hFair : Fair schedule) :
    lim (fun n => (W.Chain S0 schedule n).S) = S0.S ∪ W.AllPicks := by
  ext p
  constructor
  · intro hp
    rw [W.lim_closed_form] at hp
    cases hp with
    | inl hS0 => exact Or.inl hS0
    | inr hall =>
      obtain ⟨i, hpeq⟩ := hall
      exact Or.inr ⟨schedule i, hpeq⟩
  · intro hp
    cases hp with
    | inl hS0 =>
      rw [mem_lim]
      exact ⟨0, hS0⟩
    | inr hall =>
      exact W.lim_contains_all_picks S0 schedule hFair hall

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) OmegaState and Invariance
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Soundness of AllPicks. -/
theorem all_picks_sound : Sound W.Truth W.AllPicks := by
  intro p hp
  obtain ⟨i, hpeq⟩ := hp
  rw [hpeq]
  exact W.pick_true i

/-- Sound is stable under binary union. -/
theorem sound_union (A B : Set PropT) (hA : Sound W.Truth A) (hB : Sound W.Truth B) :
    Sound W.Truth (A ∪ B) := by
  intro p hp
  cases hp with
  | inl h => exact hA p h
  | inr h => exact hB p h

/-- The canonical ω-state: S0 ∪ AllPicks. -/
def omegaState (S0 : W.State) : W.State where
  S := S0.S ∪ W.AllPicks
  sound := W.sound_union S0.S W.AllPicks S0.sound W.all_picks_sound

/-- Schedule invariance: two fair schedules produce the same limit. -/
theorem lim_eq_of_fair_schedules (S0 : W.State)
    (schedule₁ schedule₂ : ℕ → Index)
    (hFair₁ : Fair schedule₁) (hFair₂ : Fair schedule₂) :
    lim (fun n => (W.Chain S0 schedule₁ n).S) =
    lim (fun n => (W.Chain S0 schedule₂ n).S) := by
  rw [W.lim_schedule_free S0 schedule₁ hFair₁]
  rw [W.lim_schedule_free S0 schedule₂ hFair₂]

/-- Limit equals omegaState under fair schedule. -/
theorem lim_eq_omegaState (S0 : W.State) (schedule : ℕ → Index) (hFair : Fair schedule) :
    lim (fun n => (W.Chain S0 schedule n).S) = (W.omegaState S0).S := by
  rw [W.lim_schedule_free S0 schedule hFair]
  rfl

/-- Minimality: omegaState is the smallest sound extension containing all picks. -/
theorem omegaState_minimal (S0 : W.State) (T : Set PropT)
    (hBase : S0.S ⊆ T) (hPicks : W.AllPicks ⊆ T) :
    (W.omegaState S0).S ⊆ T := by
  intro p hp
  cases hp with
  | inl h => exact hBase h
  | inr h => exact hPicks h

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Constructive Schedule Existence
-- ═══════════════════════════════════════════════════════════════════════════════

section Encodable

variable [Encodable Index] [Inhabited Index]

/-- Canonical schedule from Encodable. -/
def scheduleOfEncodable : ℕ → Index :=
  fun n => Option.getD (Encodable.decode n) default

/-- The canonical schedule is fair. -/
theorem scheduleOfEncodable_fair : Fair (scheduleOfEncodable (Index := Index)) := by
  intro i
  use Encodable.encode i
  unfold scheduleOfEncodable
  simp only [Encodable.encodek, Option.getD_some]

/-- Existence of fair schedule reaching omegaState. -/
theorem exists_fair_limit_eq_omegaState (S0 : W.State) :
    ∃ schedule : ℕ → Index,
      Fair schedule ∧
      lim (fun n => (W.Chain S0 schedule n).S) = (W.omegaState S0).S := by
  use scheduleOfEncodable (Index := Index)
  constructor
  · exact scheduleOfEncodable_fair
  · exact W.lim_eq_omegaState S0 scheduleOfEncodable scheduleOfEncodable_fair

end Encodable

end PickWorld

-- ═══════════════════════════════════════════════════════════════════════════════
-- 9) Summary: The Abstract Pattern
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## What This Captures

The dynamics depends ONLY on:
1. A type of indices (Index)
2. A type of propositions (PropT)
3. A truth predicate (Truth)
4. A pick function with truth proof

Given these, we get FOR FREE:
- Soundness preservation (chain_sound, lim_sound)
- Closed form characterization (chain_closed_form, lim_closed_form)
- Schedule independence (lim_eq_of_fair_schedules)
- Canonical ω-state (omegaState)
- Minimality (omegaState_minimal)
- Constructive existence of fair schedule (exists_fair_limit_eq_omegaState)

## The Separation

- **Structure**: StructuralDichotomy provides O, ker_iff, sig_invar
- **EM**: Needed only for sig_iff_ne_bot (deciding the side)
- **Dynamics**: PickWorld provides navigation, independent of how picks are determined

## For P vs NP

To apply this pattern:
1. Find an operator O natural in a poly-constrained category
2. Prove ker_iff: O x = ⊥ ↔ UNSAT x (non-tautological)
3. Prove sig_invar: SAT (O x) ↔ SAT x
4. Then dynamics follows automatically

The open question: does such an O exist for SAT/UNSAT?
-/

end RevHalt.AbstractDynamics
