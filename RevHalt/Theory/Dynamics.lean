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
-- 3) step: the transition function
-- =====================================================================================

/--
  A single step of the dynamics.

  Given:
  - A current state `st`
  - A code `e`
  - An oracle pick for `e`
  - The encoding correctness hypotheses

  Returns: a new state with `pick.p` added, soundness preserved.

  Note: We don't require `¬ S.Provable pick.p` here — that's a "strictness" condition
  for frontier membership, not for soundness.
-/
def step
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (st : State PropT Truth)
    (e : Code)
    (pick : OraclePick Sys encode_halt encode_not_halt e) :
    State PropT Truth where
  S := st.S ∪ {pick.p}
  sound := by
    -- prove soundness of st.S ∪ {pick.p}
    have hTruthPick : Truth pick.p := by
      cases pick.cert with
      | inl h =>
          have hKit : Rev0_K Sys.K (Sys.Machine e) := h.1
          have hpEq : pick.p = encode_halt e := h.2
          rw [hpEq]
          exact h_pos e hKit
      | inr h =>
          have hStab : KitStabilizes Sys.K (Sys.Machine e) := h.1
          have hpEq : pick.p = encode_not_halt e := h.2
          rw [hpEq]
          exact h_neg e hStab
    exact sound_union_singleton Truth st.S pick.p st.sound hTruthPick

/-- The step is monotone: the corpus grows. -/
theorem step_mono
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (st : State PropT Truth)
    (e : Code)
    (pick : OraclePick Sys encode_halt encode_not_halt e) :
    st.S ⊆ (step Sys Truth encode_halt encode_not_halt h_pos h_neg st e pick).S := by
  intro p hp
  exact Or.inl hp

-- =====================================================================================
-- 4) Chain: iteration of steps
-- =====================================================================================

/--
  A chain is an iteration of steps, parameterized by:
  - `schedule : ℕ → Code` — which code to process at each step
  - `picks : ∀ n, OraclePick ...` — the certificate for each code
-/
def Chain
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n)) :
    ℕ → State PropT Truth
  | 0 => S0
  | n + 1 =>
      step Sys Truth encode_halt encode_not_halt h_pos h_neg
        (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n)
        (schedule n)
        (picks n)

/-- Chain monotonicity: `Chain n ⊆ Chain (n+1)`. -/
theorem chain_mono
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n))
    (n : ℕ) :
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).S ⊆
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks (n + 1)).S := by
  exact step_mono Sys Truth encode_halt encode_not_halt h_pos h_neg
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n)
    (schedule n) (picks n)

/-- All states in the chain are sound (by construction). -/
theorem chain_sound_all
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n))
    (n : ℕ) :
    Sound Truth (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).S :=
  (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).sound

-- =====================================================================================
-- 5) lim: the limit of a chain
-- =====================================================================================

/-- The limit of a chain is the union of all states. -/
def lim {PropT : Type} (C : ℕ → Set PropT) : Set PropT :=
  { p | ∃ n, p ∈ C n }

/-- The limit of a sound chain is sound. -/
theorem lim_sound
    {PropT : Type}
    (Truth : PropT → Prop)
    (C : ℕ → Set PropT)
    (hSound : ∀ n, Sound Truth (C n)) :
    Sound Truth (lim C) := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  exact hSound n p hn

/-- Specialized: the limit of a navigation chain is sound. -/
theorem chain_lim_sound
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n)) :
    Sound Truth (lim (fun n => (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).S)) := by
  apply lim_sound Truth
  intro n
  exact chain_sound_all Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n

-- =====================================================================================
-- 6) Cumulative monotonicity
-- =====================================================================================

/-- General monotonicity: m ≤ n → Chain m ⊆ Chain n. -/
theorem chain_mono_le
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n))
    (m n : ℕ) (h : m ≤ n) :
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks m).S ⊆
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).S := by
  induction n with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero h
      rw [this]
  | succ k ih =>
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
          have hStep := chain_mono Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks k
          exact Set.Subset.trans (ih hmk) hStep
      | inr heq =>
          rw [heq]

/-- Every state is contained in the limit. -/
theorem chain_subset_lim
    {Code PropT : Type}
    (Sys : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K Sys.K (Sys.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes Sys.K (Sys.Machine e) → Truth (encode_not_halt e))
    (S0 : State PropT Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick Sys encode_halt encode_not_halt (schedule n))
    (n : ℕ) :
    (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks n).S ⊆
    lim (fun m => (Chain Sys Truth encode_halt encode_not_halt h_pos h_neg S0 schedule picks m).S) := by
  intro p hp
  exact ⟨n, hp⟩

end RevHalt
