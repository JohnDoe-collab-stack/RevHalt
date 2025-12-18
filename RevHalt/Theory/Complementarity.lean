import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.Complementarity

T3: Complementarity Theorem — S₁ ∪ S₂ = S₃

## Core Decomposition (Typed Definitions)

- **S₁** := `S1Set S encode_halt` (non-internalizable)
- **S₂** := parameter `S2 : Set PropT` (internalizable base)
- **S₃** := `S3Set S S2 encode_halt` = S₂ ∪ S₁

## Explicit Kit Dependency (Types)

```
S : ImpossibleSystem Code PropT
S.K : RHKit
S.h_canon : DetectsMonotone S.K
Rev0_K S.K : Trace → Prop
```

## S₁ Membership (Typed)

`p ∈ S1Set S encode_halt` iff:
- `∃ e, p = encode_halt e`
- `Rev0_K S.K (S.Machine e)` (Kit certifies)
- `¬ S.Provable (encode_halt e)` (non-internalizable)

## Main Results
- `S1Set`, `S3Set`: Explicit type definitions
- `mem_S1Set_of_witness`: Membership lemma
- `S1Set_nonempty_of_witness`: S₁ ≠ ∅ given witness
- `exists_unprovable_encode_halt`: ∃ unprovable encoding (weaker than S₁ ≠ ∅)
- `T3_weak_extension_explicit`: S₃ = S₁ ∪ S₂ is sound
- `InfiniteIndependentHalting`: |S₁| = ∞ (Kit-certified AND unprovable)
- `T3_strong`: Multiple S₃ₙ from S₁ partitions
-/

namespace RevHalt

-- ==============================================================================================
-- T3: Complementarity — Explicit Definitions
-- ==============================================================================================

/-
  ## Typed Decomposition

  **S₁** := `S1Set S encode_halt : Set PropT`
         = { p | ∃ e, p = encode_halt e ∧ Rev0_K S.K (Machine e) ∧ ¬Provable (encode_halt e) }

  **S₂** := parameter (internalizable base theory)

  **S₃** := `S3Set S S2 encode_halt : Set PropT`
         = S₂ ∪ S₁

  Kit dependency:
  - `S.K : RHKit`
  - `S.h_canon : DetectsMonotone S.K`
  - `Rev0_K S.K : Trace → Prop`
-/

-- ==============================================================================================
-- Explicit S₁ and S₃ Definitions
-- ==============================================================================================

/-- Explicit Kit extraction with visible `RHKit` type. -/
abbrev KitOf {Code PropT : Type} (S : ImpossibleSystem Code PropT) : RHKit := S.K

/-- **S₁** := Non-internalizable set.
    Uses `KitOf S : RHKit` explicitly.
    `p ∈ S1Set` iff `p = encode_halt e` for some `e` with Kit-certified halting and unprovable. -/
def S1Set {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) : Set PropT :=
  let K : RHKit := KitOf S  -- Explicit Kit with RHKit type
  { p | ∃ e : Code,
      p = encode_halt e ∧
      Rev0_K K (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) }

/-- **S₃** := S₂ ∪ S₁ (complementary system). -/
def S3Set {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (S2 : Set PropT) (encode_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1Set S encode_halt

/-- Membership lemma: given witness (hKit, hUnprov), `encode_halt e ∈ S₁`.
    Uses explicit cast from `S.K` to `KitOf S : RHKit`. -/
lemma mem_S1Set_of_witness
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    encode_halt e ∈ S1Set S encode_halt := by
  -- Explicit cast: K = S.K = KitOf S
  have hKit' : Rev0_K (KitOf S) (S.Machine e) := by
    simpa [KitOf] using hKit
  -- Now matches literal S1Set definition
  exact ⟨e, rfl, hKit', hUnprov⟩

/-- **S₁ ≠ ∅** given a witness (e, hKit, hUnprov). -/
theorem S1Set_nonempty_of_witness
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT)
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    (S1Set S encode_halt).Nonempty := by
  exact ⟨encode_halt e, mem_S1Set_of_witness S encode_halt e hKit hUnprov⟩

-- ==============================================================================================
-- Unprovable Encoding Existence (weaker than S₁ ≠ ∅)
-- ==============================================================================================

/--
  **∃ unprovable encoding** (not the same as S₁ ≠ ∅).
  This proves only `∃ e, ¬Provable(encode_halt e)`, without Kit-certification.
-/
theorem exists_unprovable_encode_halt
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (h_sound : ∀ p, S.Provable p → Truth p)
    (encode_halt : Code → PropT)
    (h_truth_to_real : ∀ e, Truth (encode_halt e) → Rev0_K S.K (S.Machine e)) :
    ∃ e, ¬ S.Provable (encode_halt e) := by
  obtain ⟨e, he⟩ := S.diagonal_program encode_halt
  refine ⟨e, ?_⟩
  intro hProv
  have hReal : Rev0_K S.K (S.Machine e) :=
    h_truth_to_real e (h_sound _ hProv)
  have hProvNot : S.Provable (S.Not (encode_halt e)) :=
    he.mp hReal
  exact S.consistent (S.absurd (encode_halt e) hProv hProvNot)

-- ==============================================================================================
-- T3.1 (Weak) — S₃ = S₁ ∪ S₂ is Sound
-- ==============================================================================================

/--
**T3.1 — S₃ = S₁ ∪ S₂ is Sound** ("linear reading" version, without `simp`)

Same statement, same hypotheses, same conclusions; proof made entirely explicit.
-/
theorem T3_weak_extension_explicit
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (_ : ∀ p, S.Provable p → Truth p)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    ∃ S3 : Set PropT,
      S3 = S3Set S S2 encode_halt ∧           -- S₃ = S₂ ∪ S₁ (literal)
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      encode_halt e ∈ S1Set S encode_halt ∧   -- Typed S₁ membership
      encode_halt e ∈ S3 ∧
      Halts (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) := by
  -- Explicit definition of S₃
  let S3 : Set PropT := S3Set S S2 encode_halt

  -- KIT → HALTS via T1 + embedded canonical certificate
  have hHalt : Halts (S.Machine e) :=
    (T1_traces S.K S.h_canon (S.Machine e)).1 hKit

  -- Explicit membership in S₁
  have h_mem_S1 : encode_halt e ∈ S1Set S encode_halt :=
    mem_S1Set_of_witness S encode_halt e hKit hUnprov

  refine ⟨S3, rfl, ?_, ?_, h_mem_S1, ?_, hHalt, hUnprov⟩

  · -- S₂ ⊆ S₃
    intro p hp
    -- S3 = S2 ∪ S1Set ...
    exact Set.mem_union_left (S1Set S encode_halt) hp

  · -- Soundness of S₃ = sound(S₂) + sound(S₁)
    intro p hp
    -- hp : p ∈ S2 ∪ S1Set ...
    rcases hp with hp2 | hp1
    · -- case p ∈ S₂
      exact h_S2_sound p hp2
    · -- case p ∈ S₁
      -- unfold the definition of S1Set: ∃ e', p = encode_halt e' ∧ ...
      rcases hp1 with ⟨e', hpEq, hKit', _hUnprov'⟩
      -- Explicit cast: KitOf S = S.K
      have hKit'' : Rev0_K S.K (S.Machine e') := by
        simpa [KitOf] using hKit'
      have hTrue : Truth (encode_halt e') := h_encode_correct e' hKit''
      -- rewrite p via hpEq
      simpa [hpEq] using hTrue

  · -- encode_halt e ∈ S₃ (since ∈ S₁ ⊆ S₃)
    exact Set.mem_union_right S2 h_mem_S1

-- ==============================================================================================
-- Infinite S₁ Elements (Kit-certified AND non-internalizable)
-- ==============================================================================================

/--
  **Infinite S₁ elements** (full S₁, not just Kit-level).

  This captures infinitely many codes that are:
  - Kit-certified: `Rev0_K S.K (Machine (family i))` ↔ `haltsTruth i`
  - Non-internalizable: `¬ S.Provable (encode_halt (family i))`

  Together, these conditions define membership in S₁.
-/
structure InfiniteIndependentHalting (Code PropT : Type) (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) where
  Index : Type
  InfiniteIndex : Infinite Index
  family : Index → Code
  distinct : Function.Injective family
  haltsTruth : Index → Prop
  halts_agree : ∀ i, Rev0_K S.K (S.Machine (family i)) ↔ haltsTruth i
  -- S₁ condition: non-internalizable
  unprovable : ∀ i, ¬ S.Provable (encode_halt (family i))

/-- Partition of indices. -/
structure Partition (Index : Type) where
  Parts : ℕ → Set Index
  disjoint : ∀ n m, n ≠ m → Disjoint (Parts n) (Parts m)

-- ==============================================================================================
-- T3.2 (Strong) — Multiple S₃ₙ from S₁ Partitions
-- ==============================================================================================

/--
**T3.2 — Multiple complementary systems from S₁ partitions**

Given infinite **S₁ elements** (Kit-certified AND unprovable),
constructs {S₃ₙ} family. Each S₃ₙ = S₂ ∪ (encoded partition elements of S₁).
-/
theorem T3_strong {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt : Code → PropT)
    (encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ Rev0_K S.K (S.Machine e) → Truth (encode_not_halt e))
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (indep : InfiniteIndependentHalting Code PropT S encode_halt)  -- Now takes encode_halt
    (partition : Partition indep.Index)
    : ∃ (S3_family : ℕ → Set PropT),
        (∀ n, S2 ⊆ S3_family n) ∧
        (∀ n, ∀ p ∈ S3_family n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j) := by
  classical
  let encode : indep.Index → PropT := fun i =>
    if indep.haltsTruth i then encode_halt (indep.family i)
    else encode_not_halt (indep.family i)
  let S3_family : ℕ → Set PropT := fun n =>
    S2 ∪ { p | ∃ i ∈ partition.Parts n, p = encode i }
  use S3_family
  refine ⟨?_, ?_, ?_⟩
  · -- S₂ ⊆ S₃ₙ
    intro n p hp
    exact Set.mem_union_left _ hp
  · -- S₃ₙ is sound
    intro n p hp
    cases hp with
    | inl h_S2 => exact h_S2_sound p h_S2
    | inr h_new =>
      obtain ⟨i, _, rfl⟩ := h_new
      simp only [encode]
      split_ifs with h_halts
      · have h_real : Rev0_K S.K (S.Machine (indep.family i)) := (indep.halts_agree i).mpr h_halts
        exact h_encode_correct (indep.family i) h_real
      · have h_not_real : ¬ Rev0_K S.K (S.Machine (indep.family i)) := by
          intro h_contra
          exact h_halts ((indep.halts_agree i).mp h_contra)
        exact h_encode_correct_neg (indep.family i) h_not_real
  · -- S₁-portions disjoint
    intro n m hnm i hi j hj h_eq
    have h_disj := partition.disjoint n m hnm
    rw [h_eq] at hi
    have h_inter : j ∈ partition.Parts n ⊓ partition.Parts m := ⟨hi, hj⟩
    rw [disjoint_iff.mp h_disj] at h_inter
    exact h_inter

end RevHalt
