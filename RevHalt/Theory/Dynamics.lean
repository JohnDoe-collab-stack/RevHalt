import RevHalt.Theory.Complementarity
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.Dynamics

Explicit formalization of the navigation dynamics induced by T3.

## Core Idea

The dynamics is not about "provability" (`⊢_S p`), but about **accumulating semantic commitments**
(`p ∈ S` with `Sound S`). Each step consumes a certificate (Σ₁ or Π₁) and extends the corpus.

## Structures

- `Sound Truth S`: all members of S are true
- `State`: a set S equipped with a proof of soundness
- `DynamicsSpec`: packages all parameters (Sys, Truth, encodings, correctness)
- `step`: transition S → S ∪ {pick.p} preserving soundness
- `Chain`: iteration of steps indexed by ℕ
- `lim`: limit (union) of a chain

## Key Theorems

- `chain_mono`: `(Chain n).S ⊆ (Chain (n+1)).S`
- `chain_sound_all`: every state in the chain is sound
- `lim_sound`: the limit is sound
-/

namespace RevHalt

-- =====================================================================================
-- 1) Sound: the fundamental invariant
-- =====================================================================================

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
  | inr hqp =>
      have : q = p := hqp
      rw [this]
      exact hp

/-- Sound is closed under arbitrary union. -/
theorem sound_iUnion {ι PropT : Type} (Truth : PropT → Prop) (S : ι → Set PropT)
    (h : ∀ i, Sound Truth (S i)) :
    Sound Truth (⋃ i, S i) := by
  intro p hp
  rw [Set.mem_iUnion] at hp
  obtain ⟨i, hi⟩ := hp
  exact h i p hi

-- =====================================================================================
-- 2) State: a corpus with its soundness proof
-- =====================================================================================

/-- A state is a corpus S together with a proof that S is sound. -/
structure State (PropT : Type) (Truth : PropT → Prop) where
  S : Set PropT
  sound : Sound Truth S

/-- The initial (empty) state. -/
def State.empty {PropT : Type} (Truth : PropT → Prop) : State PropT Truth where
  S := ∅
  sound := sound_empty Truth

-- =====================================================================================
-- 3) DynamicsSpec: package all parameters
-- =====================================================================================

/--
  A dynamics specification packages all the parameters needed for navigation:
  - The complementarity system (Sys)
  - The truth predicate (Truth)
  - The encoding functions (encode_halt, encode_not_halt)
  - The correctness hypotheses (h_pos, h_neg)
-/
structure DynamicsSpec (Code PropT : Type) where
  Sys : ComplementaritySystem Code PropT
  Truth : PropT → Prop
  encode_halt : Code → PropT
  encode_not_halt : Code → PropT
  h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e)
  h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e)

-- =====================================================================================
-- 4) truth_of_pick: factored lemma
-- =====================================================================================

/--
  **Factored Lemma**: Extract truth from any oracle pick.
  This is the core semantic content of each navigation step.
-/
theorem truth_of_pick
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e) :
    D.Truth pick.p := by
  cases pick.cert with
  | inl h =>
      have hKit : Rev0_K D.Sys.K (D.Sys.Machine e) := h.1
      have hpEq : pick.p = D.encode_halt e := h.2
      rw [hpEq]
      exact D.h_pos e hKit
  | inr h =>
      have hStab : KitStabilizes D.Sys.K (D.Sys.Machine e) := h.1
      have hpEq : pick.p = D.encode_not_halt e := h.2
      rw [hpEq]
      exact D.h_neg e hStab

-- =====================================================================================
-- 5) step: the transition function (using DynamicsSpec)
-- =====================================================================================

/--
  A single step of the dynamics.

  Given a current state and an oracle pick, returns a new state with pick.p added.
  Soundness is preserved via `truth_of_pick`.
-/
def step
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (st : State PropT D.Truth)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e) :
    State PropT D.Truth where
  S := st.S ∪ {pick.p}
  sound := sound_union_singleton D.Truth st.S pick.p st.sound (truth_of_pick D e pick)

/-- The step is monotone: the corpus grows. -/
theorem step_mono
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (st : State PropT D.Truth)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e) :
    st.S ⊆ (step D st e pick).S := by
  intro p hp
  exact Or.inl hp

-- =====================================================================================
-- 6) prefixPicks: closed form of accumulated picks
-- =====================================================================================

/-- The set of pick sentences from indices 0 to n-1. -/
def prefixPicks {PropT : Type} (picks : ℕ → PropT) (n : ℕ) : Set PropT :=
  { p | ∃ i, i < n ∧ p = picks i }

theorem mem_prefixPicks {PropT : Type} (picks : ℕ → PropT) (n : ℕ) (p : PropT) :
    p ∈ prefixPicks picks n ↔ ∃ i, i < n ∧ p = picks i := Iff.rfl

theorem prefixPicks_zero {PropT : Type} (picks : ℕ → PropT) :
    prefixPicks picks 0 = ∅ := by
  ext p
  constructor
  · intro ⟨i, hi, _⟩
    exact False.elim (Nat.not_lt_zero i hi)
  · intro h
    exact False.elim h

theorem prefixPicks_succ {PropT : Type} (picks : ℕ → PropT) (n : ℕ) :
    prefixPicks picks (n + 1) = prefixPicks picks n ∪ {picks n} := by
  ext p
  constructor
  · intro ⟨i, hi, hpeq⟩
    cases Nat.lt_succ_iff_lt_or_eq.mp hi with
    | inl hlt => exact Or.inl ⟨i, hlt, hpeq⟩
    | inr heq => rw [heq] at hpeq; exact Or.inr hpeq
  · intro h
    cases h with
    | inl hpre =>
        obtain ⟨i, hi, hpeq⟩ := hpre
        exact ⟨i, Nat.lt_succ_of_lt hi, hpeq⟩
    | inr hsingle =>
        exact ⟨n, Nat.lt_succ_self n, hsingle⟩

theorem prefixPicks_mono {PropT : Type} (picks : ℕ → PropT) (m n : ℕ) (h : m ≤ n) :
    prefixPicks picks m ⊆ prefixPicks picks n := by
  intro p ⟨i, hi, hpeq⟩
  exact ⟨i, Nat.lt_of_lt_of_le hi h, hpeq⟩

-- =====================================================================================
-- 7) Chain: iteration of steps
-- =====================================================================================

/--
  A chain is an iteration of steps, parameterized by:
  - `schedule : ℕ → Code` — which code to process at each step
  - `picks : ∀ n, OraclePick ...` — the certificate for each code
-/
def Chain
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n)) :
    ℕ → State PropT D.Truth
  | 0 => S0
  | n + 1 =>
      step D
        (Chain D S0 schedule picks n)
        (schedule n)
        (picks n)

/-- Chain monotonicity: `Chain n ⊆ Chain (n+1)`. -/
theorem chain_mono
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (n : ℕ) :
    (Chain D S0 schedule picks n).S ⊆
    (Chain D S0 schedule picks (n + 1)).S := by
  exact step_mono D (Chain D S0 schedule picks n) (schedule n) (picks n)

/-- All states in the chain are sound (by construction). -/
theorem chain_sound_all
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (n : ℕ) :
    Sound D.Truth (Chain D S0 schedule picks n).S :=
  (Chain D S0 schedule picks n).sound

/-- General monotonicity: m ≤ n → Chain m ⊆ Chain n. -/
theorem chain_mono_le
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (m n : ℕ) (h : m ≤ n) :
    (Chain D S0 schedule picks m).S ⊆
    (Chain D S0 schedule picks n).S := by
  induction n with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero h
      rw [this]
  | succ k ih =>
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
          have hStep := chain_mono D S0 schedule picks k
          exact Set.Subset.trans (ih hmk) hStep
      | inr heq =>
          rw [heq]

-- =====================================================================================
-- 8) lim: the limit of a chain (using iUnion)
-- =====================================================================================

/-- The limit of a chain is the union of all states. -/
def lim {PropT : Type} (C : ℕ → Set PropT) : Set PropT := ⋃ n, C n

theorem mem_lim {PropT : Type} {C : ℕ → Set PropT} {p : PropT} :
    p ∈ lim C ↔ ∃ n, p ∈ C n := by
  unfold lim
  rw [Set.mem_iUnion]

/-- The limit of a sound chain is sound. -/
theorem lim_sound
    {PropT : Type}
    (Truth : PropT → Prop)
    (C : ℕ → Set PropT)
    (hSound : ∀ n, Sound Truth (C n)) :
    Sound Truth (lim C) := by
  unfold lim
  exact sound_iUnion Truth C hSound

/-- Specialized: the limit of a navigation chain is sound. -/
theorem chain_lim_sound
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n)) :
    Sound D.Truth (lim (fun n => (Chain D S0 schedule picks n).S)) := by
  apply lim_sound D.Truth
  intro n
  exact chain_sound_all D S0 schedule picks n

/-- Every state is contained in the limit. -/
theorem chain_subset_lim
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (n : ℕ) :
    (Chain D S0 schedule picks n).S ⊆
    lim (fun m => (Chain D S0 schedule picks m).S) := by
  intro p hp
  rw [mem_lim]
  exact ⟨n, hp⟩

-- =====================================================================================
-- 9) Schedule properties (without Provable)
-- =====================================================================================

/-- A schedule is fair if every code appears at least once. -/
def Fair {Code : Type} (schedule : ℕ → Code) : Prop :=
  ∀ e : Code, ∃ n : ℕ, schedule n = e

/-- A schedule is infinitely fair if every code appears infinitely often. -/
def InfinitelyFair {Code : Type} (schedule : ℕ → Code) : Prop :=
  ∀ e : Code, ∀ N : ℕ, ∃ n : ℕ, n > N ∧ schedule n = e

theorem infinitely_fair_implies_fair {Code : Type} (schedule : ℕ → Code)
    (h : InfinitelyFair schedule) :
    Fair schedule := by
  intro e
  obtain ⟨n, _, hn⟩ := h e 0
  exact ⟨n, hn⟩

-- =====================================================================================
-- 10) Dynamics comparison
-- =====================================================================================

/-- If two chains are pointwise included, their limits are included. -/
theorem lim_mono {PropT : Type} (C D : ℕ → Set PropT)
    (h : ∀ n, C n ⊆ D n) :
    lim C ⊆ lim D := by
  intro p hp
  rw [mem_lim] at hp ⊢
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, h n hn⟩

end RevHalt
