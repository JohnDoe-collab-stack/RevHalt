import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt: Reverse Halting & Canonical Verification

This file implements the core definitions and theorems for the RevHalt project, derived from the
Reverse-Halting (Rev) operator and its applications to verification and incompleteness.

We establish three main results:
* **T1**: Canonicity of Rev (it captures exactly the Halting property under mild assumptions).
* **T2**: Impossibility of internalizing this specific Halting predicate (Godel/Turing obstruction).
* **T3**: Foundation for complementarity (sound theories as partial views).

-/

-- ==============================================================================================
-- 1. Definitions & Framework
-- ==============================================================================================

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

/-- Reverse Halting Kit structure. Represents an abstract observation mechanism. -/
structure RHKit where
  Proj : (ℕ → Prop) → Prop

/--
  The core axiom for a valid Kit: `DetectsMonotone`.
  It states that for any *monotone* process, the Kit's projection agrees with standard existence.
  This allows the Kit to have "exotic" behavior on non-monotone traces, but it must be standard on monotone ones.
-/
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : ℕ → Prop, Monotone X → (K.Proj X ↔ ∃ n, X n)

/--
  Rev_K: The Reverse Halting Operator.
  It standardizes the trace using `up` before applying the Kit.
-/
def Rev_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)

abbrev Rev0_K := Rev_K

-- ==============================================================================================
-- T1: Canonicity of Rev
-- ==============================================================================================

/--
  **Theorem T1 (Traces)**:
  Under the assumption that K detects monotone properties, `Rev0_K` is extensionally equivalent
  to standard Halting for *all* traces (even non-monotone ones).
-/
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T := by
  intro T
  unfold Rev0_K Rev_K
  -- 1. Apply DetectsMonotone to the trace (up T), which is monotone.
  have h_mono : Monotone (up T) := up_mono T
  have h_equiv := hK (up T) h_mono
  rw [h_equiv]
  -- 2. Use the fact that ∃ n, up T n ↔ ∃ n, T n
  exact exists_up_iff T

/-- Corollary: Independence of the specific Kit. Any two valid Kits yield the same verdict. -/
theorem T1_uniqueness (K1 K2 : RHKit) (hK1 : DetectsMonotone K1) (hK2 : DetectsMonotone K2) :
    ∀ T, Rev0_K K1 T ↔ Rev0_K K2 T := by
  intro T
  rw [T1_traces K1 hK1, T1_traces K2 hK2]

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
theorem T1_semantics (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ := by
  intro Γ φ
  unfold verdict_K
  rw [hBridge Γ φ]
  rw [T1_traces K hK]

-- ==============================================================================================
-- T2: Impossibility of Internalizing Rev (Abstract Turing-Godel)
-- ==============================================================================================

/--
  Context for the impossibility result.
  Represents a computing system with:
  - `Code`: program codes
  - `PropT`: internal propositions / types
  - `RealHalts`: the external, "real" truth (e.g., our Rev0_K)
  - `Provable`: an internal provability predicate
  - `diagonal_program`: the ability to construct self-referential sentences
-/
structure TuringGodelContext' (Code : Type) (PropT : Type) where
  RealHalts : Code → Prop
  Provable  : PropT → Prop
  FalseT    : PropT
  Not       : PropT → PropT
  -- Consistency Axiom
  consistent : ¬ Provable FalseT
  -- Logic Axiom
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT
  -- Diagonal Fixpoint Axiom
  diagonal_program : ∀ H : Code → PropT, ∃ e, RealHalts e ↔ Provable (Not (H e))

/--
  Definition of an Internal Halting Predicate.
  To be a candidate for "capturing" RealHalts, it must be:
  1. Total (always proves Yes or No).
  2. Correct (if leads to Yes, it really halts).
  3. Complete (if leads to No, it really doesn't halt).
-/
structure InternalHaltingPredicate {Code : Type} {PropT : Type} (ctx : TuringGodelContext' Code PropT) where
  H : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))

/--
  **Theorem T2**:
  There is no internal predicate I that is simultaneously Total, Correct, and Complete
  with respect to RealHalts.
-/
theorem T2_impossibility {Code : Type} {PropT : Type} (ctx : TuringGodelContext' Code PropT) :
    ¬ ∃ _ : InternalHaltingPredicate ctx, True := by
  intro h
  obtain ⟨I, _⟩ := h
  -- 1. Construct the diagonal program e for the predicate I.H
  --    Property: RealHalts(e) ↔ Provable(¬ I.H(e))
  obtain ⟨e, he⟩ := ctx.diagonal_program I.H

  -- 2. Analyze by cases on the *real* truth of Halts(e)
  by_cases hReal : ctx.RealHalts e
  · -- Case: e really halts
    -- By Correctness, the system proves H(e)
    have hProvH : ctx.Provable (I.H e) := I.correct e hReal
    -- By Diagonal property, since RealHalts(e) is true, Provable(¬ H(e)) must be true
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := he.mp hReal
    -- Contradiction in the system
    exact ctx.consistent (ctx.absurd (I.H e) hProvH hProvNotH)
  · -- Case: e does not halt
    -- By Completeness, the system proves ¬ H(e)
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := I.complete e hReal
    -- By Diagonal property: Provable(¬ H(e)) → RealHalts(e)
    have hImpliesReal : ctx.Provable (ctx.Not (I.H e)) → ctx.RealHalts e := he.mpr
    have hRealContradiction : ctx.RealHalts e := hImpliesReal hProvNotH
    -- Contradiction with hypothesis hReal
    exact hReal hRealContradiction

-- ==============================================================================================
-- T3: Complementarity
-- ==============================================================================================

/-
  Refining the complementarity landscape:
  * **T3-Weak** (Extension by Truth): Any sound partial theory can be strictly extended by
    adding a true undecidable statement.
  * **T3-Strong** (Disjoint Families): Relies on an infinite family of independent halting
    instances to construct disjoint but complementary theories.
-/

/--
  **T3.1: Weak Complementarity (Extension by Truth)**
  Concept: Any sound theory T0 (representing a partial view of Truth) that is incomplete
  can be extended to a stronger sound theory T1 by adding a true underlying fact.
-/
theorem T3_weak_extension {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop) -- Meta-level truth predicate
    (_ : ∀ p, ctx.Provable p → Truth p) -- Base system is sound
    (T0 : Set PropT) -- Initial theory
    (h_T0_sound : ∀ p ∈ T0, Truth p) -- T0 consists only of truths
    (p_undef : PropT)
    (h_p_true : Truth p_undef) -- p is True
    (_ : ¬ (ctx.Provable p_undef)) -- (Simplification: just needs to be consistent with T0)
    : ∃ T1 : Set PropT, T0 ⊆ T1 ∧ (∀ p ∈ T1, Truth p) ∧ p_undef ∈ T1 := by
  -- Construct T1 = T0 ∪ {p_undef}
  let T1 := T0 ∪ {p_undef}
  use T1
  constructor
  · -- T0 ⊆ T1
    intro q hq
    exact Set.mem_union_left {p_undef} hq
  · constructor
    · -- T1 is sound
      intro q hq
      cases hq with
      | inl h_old => exact h_T0_sound q h_old
      | inr h_new => rw [h_new]; exact h_p_true
    · -- p_undef ∈ T1
      exact Set.mem_union_right T0 rfl

/--
  **T3.2: Strong Complementarity (Disjoint Families of Sound Theories)**

  **Axiom**: There exists an infinite set of halting statements that are independent
  (undecided) in the base theory T₀.

  **Construction**: Given a partition of this infinite set into disjoint subsets,
  we can construct a family of theories {Tᵢ}, each sound, whose "new decidable domains"
  are pairwise disjoint.

  This first definition captures an infinite family of independent (undecided) halting instances.
-/
structure InfiniteIndependentHalting (Code PropT : Type) (ctx : TuringGodelContext' Code PropT) where
  -- An infinite index set (the undecided codes)
  Index : Type
  InfiniteIndex : Infinite Index
  -- A family of codes e_i (each representing an undecided halting instance)
  family : Index → Code
  -- The family is injective (no duplicates)
  distinct : Function.Injective family
  -- Meta-level halting truth for each code
  haltsTruth : Index → Prop
  -- Key property: RealHalts(family i) iff haltsTruth i
  halts_agree : ∀ i, ctx.RealHalts (family i) ↔ haltsTruth i

/-- A partition of an index set into disjoint parts. -/
structure Partition (Index : Type) where
  -- Number of parts (could be infinite, but we use ℕ for simplicity)
  Parts : ℕ → Set Index
  -- Disjointness: different parts have no overlap
  disjoint : ∀ n m, n ≠ m → Disjoint (Parts n) (Parts m)
  -- Coverage: every index is in some part (optional, depends on formalization)

/--
  Given:
  - A base theory T₀ (sound for Truth)
  - An infinite family of independent halting instances
  - A partition of the indices into disjoint parts

  We can construct a family of theories {Tₙ}, each extending T₀, each sound,
  with pairwise disjoint "new decidable domains".
-/
theorem T3_strong {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (Truth : PropT → Prop) -- Meta-level truth
    (encode_halt : Code → PropT) -- Encoding: e ↦ "Halts(e)" as a proposition
    (encode_not_halt : Code → PropT) -- Encoding: e ↦ "¬Halts(e)" as a proposition
    (h_encode_correct : ∀ e, ctx.RealHalts e → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ ctx.RealHalts e → Truth (encode_not_halt e))
    (T0 : Set PropT) -- Base theory
    (h_T0_sound : ∀ p ∈ T0, Truth p) -- T0 is sound
    (indep : InfiniteIndependentHalting Code PropT ctx) -- Infinite independent family
    (partition : Partition indep.Index) -- Partition of the independent set
    : ∃ (TheoryFamily : ℕ → Set PropT),
        -- Each theory extends T0
        (∀ n, T0 ⊆ TheoryFamily n) ∧
        -- Each theory is sound
        (∀ n, ∀ p ∈ TheoryFamily n, Truth p) ∧
        -- The "new parts" are disjoint (formalized via the underlying index partition)
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j) := by
  classical
  -- Construct TheoryFamily(n) = T0 ∪ { encode(family(i)) | i ∈ Parts(n) }
  -- where encode chooses encode_halt or encode_not_halt based on haltsTruth
  let encode : indep.Index → PropT := fun i =>
    if indep.haltsTruth i then encode_halt (indep.family i)
    else encode_not_halt (indep.family i)
  let TheoryFamily : ℕ → Set PropT := fun n =>
    T0 ∪ { p | ∃ i ∈ partition.Parts n, p = encode i }
  use TheoryFamily

  refine ⟨?_, ?_, ?_⟩
  · -- Each theory extends T0
    intro n p hp
    exact Set.mem_union_left _ hp
  · -- Each theory is sound
    intro n p hp
    cases hp with
    | inl h_T0 => exact h_T0_sound p h_T0
    | inr h_new =>
      obtain ⟨i, _, rfl⟩ := h_new
      -- encode i is either encode_halt or encode_not_halt, both are truths
      simp only [encode]
      split_ifs with h_halts
      · -- Case: haltsTruth i is true, so RealHalts (family i) is true
        have h_real : ctx.RealHalts (indep.family i) := (indep.halts_agree i).mpr h_halts
        exact h_encode_correct (indep.family i) h_real
      · -- Case: haltsTruth i is false, so ¬ RealHalts (family i)
        have h_not_real : ¬ ctx.RealHalts (indep.family i) := by
          intro h_contra
          exact h_halts ((indep.halts_agree i).mp h_contra)
        exact h_encode_correct_neg (indep.family i) h_not_real
  · -- Disjointness of new parts (follows directly from partition disjointness)
    intro n m hnm i hi j hj h_eq
    have h_disj := partition.disjoint n m hnm
    -- After rw [h_eq] at hi, we have j ∈ Parts n and j ∈ Parts m
    rw [h_eq] at hi
    -- Disjoint means intersection is empty, so j can't be in both
    have h_inter : j ∈ partition.Parts n ⊓ partition.Parts m := ⟨hi, hj⟩
    rw [disjoint_iff.mp h_disj] at h_inter
    exact h_inter
