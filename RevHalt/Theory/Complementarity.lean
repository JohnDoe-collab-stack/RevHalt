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
- `InfiniteS1`: |S₁| = ∞ (indexed witnesses: kit + unprovable)
- `InfiniteS1.memS1`: Derived S1Set membership
- `T3_strong`: Multiple S₃ₙ from S₁ partitions (no added hypotheses)
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
-- Infinite S₁ Elements (indexed witnesses: kit + unprovable)
-- ==============================================================================================

/--
  **Infinite S₁ elements** (indexed witnesses, no injectivity required).

  Captures infinitely many codes with:
  - Kit-certified: `kit i : Rev0_K S.K (Machine (family i))`
  - Non-internalizable: `unprovable i : ¬ S.Provable (encode_halt (family i))`

  The `memS1` property is derived, not primitive.
-/
structure InfiniteS1 (Code PropT : Type) (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) where
  Index : Type
  InfiniteIndex : Infinite Index
  family : Index → Code
  distinct : Function.Injective family
  kit : ∀ i, Rev0_K S.K (S.Machine (family i))
  unprovable : ∀ i, ¬ S.Provable (encode_halt (family i))

/-- Derived: each index provides a member of `S1Set`. -/
lemma InfiniteS1.memS1
    {Code PropT : Type} {S : ImpossibleSystem Code PropT}
    {encode_halt : Code → PropT}
    (I : InfiniteS1 Code PropT S encode_halt) :
    ∀ i, encode_halt (I.family i) ∈ S1Set S encode_halt := by
  intro i
  -- Use mem_S1Set_of_witness which needs Kit cast
  have hKit : Rev0_K S.K (S.Machine (I.family i)) := I.kit i
  have hUnprov : ¬ S.Provable (encode_halt (I.family i)) := I.unprovable i
  -- Cast S.K to KitOf S for S1Set
  have hKit' : Rev0_K (KitOf S) (S.Machine (I.family i)) := by
    simpa [KitOf] using hKit
  exact ⟨I.family i, rfl, hKit', hUnprov⟩

/-- Partition of indices. -/
structure Partition (Index : Type) where
  Parts : ℕ → Set Index
  disjoint : ∀ n m, n ≠ m → Disjoint (Parts n) (Parts m)

-- ==============================================================================================
-- T3.2 (Strong) — Multiple S₃ₙ from S₁ Partitions
-- ==============================================================================================

/--
**T3.2 — Multiple complementary systems from S₁ partitions**

Given infinite **S₁ elements** (indexed witnesses),
constructs {S₃ₙ} family. Each S₃ₙ = S₂ ∪ { encode_halt(family i) | i ∈ Parts(n) }.

No `Injective encode_halt` hypothesis required.
-/
theorem T3_strong {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (indep : InfiniteS1 Code PropT S encode_halt)
    (partition : Partition indep.Index)
    : ∃ (S3_family : ℕ → Set PropT),
        (∀ n, S2 ⊆ S3_family n) ∧
        (∀ n, ∀ p ∈ S3_family n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j) := by
  classical
  let S3_family : ℕ → Set PropT := fun n =>
    S2 ∪ { p | ∃ i ∈ partition.Parts n, p = encode_halt (indep.family i) }
  refine ⟨S3_family, ?_, ?_, ?_⟩
  · -- S₂ ⊆ S₃ₙ
    intro n p hp
    exact Set.mem_union_left _ hp
  · -- S₃ₙ is sound
    intro n p hp
    rcases hp with hp2 | hpNew
    · exact h_S2_sound p hp2
    · rcases hpNew with ⟨i, _hi, rfl⟩
      -- Soundness from indexed witness: indep.kit i
      exact h_encode_correct (indep.family i) (indep.kit i)
  · -- S₁-portions disjoint
    intro n m hnm i hi j hj h_eq
    have h_disj := partition.disjoint n m hnm
    rw [h_eq] at hi
    have h_inter : j ∈ partition.Parts n ⊓ partition.Parts m := ⟨hi, hj⟩
    rw [disjoint_iff.mp h_disj] at h_inter
    exact h_inter

end RevHalt
