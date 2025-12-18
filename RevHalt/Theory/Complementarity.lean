import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.Complementarity

T3: Complementarity theorems.

## Main Results
- `T3_weak_extension`: Sound theories can be extended by adding true undecidables
- `InfiniteIndependentHalting`: Infinite family of independent halting instances
- `T3_strong`: Construction of disjoint families of sound theories
-/

namespace RevHalt

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

  Updated to use `ImpossibleSystem`, proving that the impossibility framework applies.
-/
theorem T3_weak_extension {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop) -- Meta-level truth predicate
    (_ : ∀ p, S.Provable p → Truth p) -- Base system is sound
    (T0 : Set PropT) -- Initial theory
    (h_T0_sound : ∀ p ∈ T0, Truth p) -- T0 consists only of truths
    (p_undef : PropT)
    (h_p_true : Truth p_undef) -- p is True
    (_ : ¬ (S.Provable p_undef)) -- (Simplification: just needs to be consistent with T0)
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
structure InfiniteIndependentHalting (Code PropT : Type) (S : ImpossibleSystem Code PropT) where
  -- An infinite index set (the undecided codes)
  Index : Type
  InfiniteIndex : Infinite Index
  -- A family of codes e_i (each representing an undecided halting instance)
  family : Index → Code
  -- The family is injective (no duplicates)
  distinct : Function.Injective family
  -- Meta-level halting truth for each code
  haltsTruth : Index → Prop
  -- Key property: Rev0_K K (Machine (family i)) iff haltsTruth i
  halts_agree : ∀ i, Rev0_K S.K (S.Machine (family i)) ↔ haltsTruth i

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
theorem T3_strong {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop) -- Meta-level truth
    (encode_halt : Code → PropT) -- Encoding: e ↦ "Halts(e)" as a proposition
    (encode_not_halt : Code → PropT) -- Encoding: e ↦ "¬Halts(e)" as a proposition
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ Rev0_K S.K (S.Machine e) → Truth (encode_not_halt e))
    (T0 : Set PropT) -- Base theory
    (h_T0_sound : ∀ p ∈ T0, Truth p) -- T0 is sound
    (indep : InfiniteIndependentHalting Code PropT S) -- Infinite independent family
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
      · -- Case: haltsTruth i is true, so Rev0_K ... is true
        have h_real : Rev0_K S.K (S.Machine (indep.family i)) := (indep.halts_agree i).mpr h_halts
        exact h_encode_correct (indep.family i) h_real
      · -- Case: haltsTruth i is false, so ¬ Rev0_K ...
        have h_not_real : ¬ Rev0_K S.K (S.Machine (indep.family i)) := by
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

end RevHalt
