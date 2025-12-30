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

-- =====================================================================================
-- 11) Closed Form of Chain
-- =====================================================================================

/-- Helper: extract the sentence from a pick at index i. -/
def pickSentence
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (i : ℕ) : PropT :=
  (picks i).p

/-- The set of all pick sentences up to index n-1. -/
def allPicks
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (n : ℕ) : Set PropT :=
  prefixPicks (pickSentence D schedule picks) n

/--
  **Closed Form Theorem**: The chain at step n equals the initial state plus all picks consumed so far.

  `(Chain n).S = S0.S ∪ { (picks i).p | i < n }`
-/
theorem chain_closed_form
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n))
    (n : ℕ) :
    (Chain D S0 schedule picks n).S = S0.S ∪ allPicks D schedule picks n := by
  induction n with
  | zero =>
      unfold Chain allPicks prefixPicks pickSentence
      ext p
      constructor
      · intro hp; exact Or.inl hp
      · intro hp
        cases hp with
        | inl hS0 => exact hS0
        | inr hpre =>
            obtain ⟨i, hi, _⟩ := hpre
            exact False.elim (Nat.not_lt_zero i hi)
  | succ k ih =>
      unfold Chain step allPicks
      rw [prefixPicks_succ]
      unfold pickSentence
      -- (Chain k).S ∪ {(picks k).p} = S0.S ∪ (prefixPicks ... k ∪ {(picks k).p})
      -- By IH: (Chain k).S = S0.S ∪ prefixPicks ... k
      ext p
      constructor
      · intro hp
        cases hp with
        | inl hChain =>
            rw [ih] at hChain
            cases hChain with
            | inl hS0 => exact Or.inl hS0
            | inr hpre => exact Or.inr (Or.inl hpre)
        | inr hpick =>
            exact Or.inr (Or.inr hpick)
      · intro hp
        cases hp with
        | inl hS0 =>
            have : p ∈ (Chain D S0 schedule picks k).S := by rw [ih]; exact Or.inl hS0
            exact Or.inl this
        | inr hunion =>
            cases hunion with
            | inl hpre =>
                have : p ∈ (Chain D S0 schedule picks k).S := by rw [ih]; exact Or.inr hpre
                exact Or.inl this
            | inr hpick =>
                exact Or.inr hpick

/-- The set of ALL pick sentences (no upper bound). -/
def allPicksUnbounded
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n)) : Set PropT :=
  { p | ∃ i, p = (picks i).p }

/--
  **Closed Form of Limit**: The ω-limit equals the initial state plus ALL pick sentences.

  `lim Chain = S0.S ∪ { (picks i).p | i : ℕ }`
-/
theorem lim_closed_form
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (schedule : ℕ → Code)
    (picks : ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n)) :
    lim (fun n => (Chain D S0 schedule picks n).S) = S0.S ∪ allPicksUnbounded D schedule picks := by
  ext p
  constructor
  · intro hp
    rw [mem_lim] at hp
    obtain ⟨n, hn⟩ := hp
    rw [chain_closed_form] at hn
    cases hn with
    | inl hS0 => exact Or.inl hS0
    | inr hpre =>
        unfold allPicks prefixPicks pickSentence at hpre
        obtain ⟨i, _, hpeq⟩ := hpre
        exact Or.inr ⟨i, hpeq⟩
  · intro hp
    cases hp with
    | inl hS0 =>
        rw [mem_lim]
        use 0
        unfold Chain
        exact hS0
    | inr hall =>
        rw [mem_lim]
        unfold allPicksUnbounded at hall
        obtain ⟨i, hpeq⟩ := hall
        use i + 1
        rw [chain_closed_form]
        apply Or.inr
        unfold allPicks prefixPicks pickSentence
        exact ⟨i, Nat.lt_succ_self i, hpeq⟩

-- =====================================================================================
-- 12) Coverage via Fair Schedule
-- =====================================================================================

/--
  A uniform pick oracle: for every code, we have a pick.
  This is the "oracle power" that provides certificates for all codes.
-/
def PickOracle
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT) : Type :=
  ∀ e : Code, OraclePick D.Sys D.encode_halt D.encode_not_halt e

/-- Derive picks from a uniform pick oracle and a schedule. -/
def picksFromOracle
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (pickOf : PickOracle D)
    (schedule : ℕ → Code) :
    ∀ n, OraclePick D.Sys D.encode_halt D.encode_not_halt (schedule n) :=
  fun n => pickOf (schedule n)

/--
  **Fair Coverage Theorem**: If the schedule is fair, then every code's pick sentence is in the limit.

  This is the canonical formulation of "ω covers all codes (given a fair schedule)".
-/
theorem fair_implies_coverage
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (pickOf : PickOracle D)
    (schedule : ℕ → Code)
    (hFair : Fair schedule) :
    ∀ e : Code, (pickOf e).p ∈ lim (fun n => (Chain D S0 schedule (picksFromOracle D pickOf schedule) n).S) := by
  intro e
  obtain ⟨n, hn⟩ := hFair e
  rw [lim_closed_form]
  apply Or.inr
  unfold allPicksUnbounded picksFromOracle
  use n
  rw [hn]

/--
  **Corollary**: Under a fair schedule, the limit contains both halt and not-halt encodings
  for every code (whichever the oracle pick selects).
-/
theorem fair_limit_complete
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (pickOf : PickOracle D)
    (schedule : ℕ → Code)
    (hFair : Fair schedule)
    (e : Code) :
    (pickOf e).p ∈ lim (fun n => (Chain D S0 schedule (picksFromOracle D pickOf schedule) n).S) ∧
    D.Truth (pickOf e).p := by
  constructor
  · exact fair_implies_coverage D S0 pickOf schedule hFair e
  · exact truth_of_pick D e (pickOf e)

-- =====================================================================================
-- 13) Progress analysis: step with frontier tracking (constructive)
-- =====================================================================================

/--
  **Progress Theorem**: step makes strict progress when the pick is new.

  This is the constructive formulation: we don't ask "is pick.p ∈ st.S?",
  we prove properties conditional on the answer.
-/
theorem step_adds_new
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (st : State PropT D.Truth)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e)
    (hNew : pick.p ∉ st.S) :
    pick.p ∈ (step D st e pick).S ∧
    st.S ⊂ (step D st e pick).S := by
  have hStep : (step D st e pick).S = st.S ∪ {pick.p} := rfl
  constructor
  · rw [hStep]; exact Or.inr rfl
  · constructor
    · exact step_mono D st e pick
    · intro hSub
      -- hSub : (step...).S ⊆ st.S, i.e., st.S ∪ {pick.p} ⊆ st.S
      have hIn : pick.p ∈ st.S ∪ {pick.p} := Or.inr rfl
      rw [hStep] at hSub
      exact hNew (hSub hIn)

/--
  **True Idempotence**: if pick.p is already present, step returns the same corpus.
  `(step D st e pick).S = st.S` when `pick.p ∈ st.S`.
-/
theorem step_idem_of_mem
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (st : State PropT D.Truth)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e)
    (hOld : pick.p ∈ st.S) :
    (step D st e pick).S = st.S := by
  have hSub : ({pick.p} : Set PropT) ⊆ st.S := by
    intro q hq
    have : q = pick.p := hq
    rw [this]
    exact hOld
  have : st.S ∪ {pick.p} = st.S := Set.union_eq_left.mpr hSub
  unfold step
  exact this

/--
  **Union characterization**: step result is always st.S ∪ {pick.p}.
-/
theorem step_eq_union
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (st : State PropT D.Truth)
    (e : Code)
    (pick : OraclePick D.Sys D.encode_halt D.encode_not_halt e) :
    (step D st e pick).S = st.S ∪ {pick.p} := rfl

-- =====================================================================================
-- 14) Lattice structure: lim as LUB (least upper bound)
-- =====================================================================================

/-- Every chain element is contained in the limit (upper bound). -/
theorem lim_upper_bound
    {PropT : Type}
    (C : ℕ → Set PropT)
    (n : ℕ) :
    C n ⊆ lim C := by
  intro p hp
  rw [mem_lim]
  exact ⟨n, hp⟩

/-- The limit is the least upper bound: if T contains all C n, then T contains lim C. -/
theorem lim_least
    {PropT : Type}
    (C : ℕ → Set PropT)
    (T : Set PropT)
    (hUB : ∀ n, C n ⊆ T) :
    lim C ⊆ T := by
  intro p hp
  rw [mem_lim] at hp
  obtain ⟨n, hn⟩ := hp
  exact hUB n hn

/-- lim is characterized as the unique set satisfying both LUB properties. -/
theorem lim_is_lub
    {PropT : Type}
    (C : ℕ → Set PropT) :
    (∀ n, C n ⊆ lim C) ∧ (∀ T, (∀ n, C n ⊆ T) → lim C ⊆ T) := by
  constructor
  · exact lim_upper_bound C
  · exact lim_least C

-- =====================================================================================
-- 15) Schedule-Free Closed Form
-- =====================================================================================

/--
  The set of ALL oracle pick sentences, independent of any schedule.
  `AllOraclePicks = { p | ∃ e, p = (pickOf e).p }`
-/
def AllOraclePicks
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (pickOf : PickOracle D) : Set PropT :=
  { p | ∃ e : Code, p = (pickOf e).p }

/--
  **Schedule-Free Closed Form Inclusion**:
  Under a fair schedule, the ω-limit contains S0 ∪ AllOraclePicks.

  The converse (limit ⊆ S0 ∪ AllOraclePicks) also holds by `lim_closed_form`.
-/
theorem lim_contains_all_oracle_picks
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (pickOf : PickOracle D)
    (schedule : ℕ → Code)
    (hFair : Fair schedule) :
    AllOraclePicks D pickOf ⊆
    lim (fun n => (Chain D S0 schedule (picksFromOracle D pickOf schedule) n).S) := by
  intro p hp
  unfold AllOraclePicks at hp
  obtain ⟨e, hpeq⟩ := hp
  have hCov := fair_implies_coverage D S0 pickOf schedule hFair e
  rw [hpeq]
  exact hCov

/--
  **Complete Schedule-Free Characterization**:
  Under a fair schedule, `lim Chain = S0.S ∪ AllOraclePicks`.

  This is the canonical characterization: the ω-corpus is exactly
  the base plus all oracle commitments.
-/
theorem lim_schedule_free
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (S0 : State PropT D.Truth)
    (pickOf : PickOracle D)
    (schedule : ℕ → Code)
    (hFair : Fair schedule) :
    lim (fun n => (Chain D S0 schedule (picksFromOracle D pickOf schedule) n).S) =
    S0.S ∪ AllOraclePicks D pickOf := by
  ext p
  constructor
  · intro hp
    rw [lim_closed_form] at hp
    cases hp with
    | inl hS0 => exact Or.inl hS0
    | inr hall =>
        unfold allPicksUnbounded picksFromOracle at hall
        obtain ⟨i, hpeq⟩ := hall
        exact Or.inr ⟨schedule i, hpeq⟩
  · intro hp
    cases hp with
    | inl hS0 =>
        rw [mem_lim]
        use 0
        unfold Chain
        exact hS0
    | inr hall =>
        exact lim_contains_all_oracle_picks D S0 pickOf schedule hFair hall

/--
  **Soundness of AllOraclePicks**: every element of AllOraclePicks is true.
-/
theorem all_oracle_picks_sound
    {Code PropT : Type}
    (D : DynamicsSpec Code PropT)
    (pickOf : PickOracle D) :
    Sound D.Truth (AllOraclePicks D pickOf) := by
  intro p hp
  unfold AllOraclePicks at hp
  obtain ⟨e, hpeq⟩ := hp
  rw [hpeq]
  exact truth_of_pick D e (pickOf e)

end RevHalt
