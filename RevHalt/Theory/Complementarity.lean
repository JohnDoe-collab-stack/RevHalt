import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.Complementarity

T3: Complementarity (one-sided) — S₁ ∪ S₂ = S₃

## Core Decomposition (Typed Definitions)

- **S₁ (one-sided frontier)** := `S1Set S encode_halt` (kit-certified + not provable in `S`)
- **S₂ (base corpus)** := parameter `S2 : Set PropT` with soundness witness `h_S2_sound`
- **S₃ (one-sided extension)** := `S3Set S S2 encode_halt` = `S₂ ∪ S₁`

### Variants

- **Two-sided oracle (local step)**: for fixed `e`, an explicit witness `OraclePick` selects either
  `encode_halt e` or `encode_not_halt e` and yields the one-step extension `S2 ∪ {pick.p}`.
- **Two-sided oracle (global frontier)**: `S1TwoSet` / `S3TwoSet` collect all oracle-chosen sentences across all codes
  (not used by the local oracle theorem in this file; intended for later globalization).

## Lean-Faithful Interpretation

- We work over a fixed syntactic universe `PropT` (so `Set PropT` is a predicate `PropT → Prop`).
- Semantics is represented externally by a truth predicate `Truth : PropT → Prop` (or, upstream, by `Sat`/`SemConsequences`).
- `S2` is an arbitrary internalizable base corpus `S2 : Set PropT` equipped with an explicit soundness witness
  `h_S2_sound : ∀ p ∈ S2, Truth p`
  (i.e. membership implies external truth).
- `S1` is the non-internalizable syntactic frontier `S1Set S encode_halt : Set PropT`, whose elements are sentences
  of type `PropT` (typically `encode_halt e`) singled out by the interaction of:
  - the external certification `Rev0_K S.K (S.Machine e)`, and
  - internal non-derivability `¬ S.Provable (encode_halt e)`.

The one-sided complementarity result is exactly the construction
`S3 := S2 ∪ S1` (implemented as `S3Set S S2 encode_halt`),
showing that the extension contains both layers, preserves semantic soundness under the stated hypotheses,
and adds kit-certified sentences from `S1` that are not internalized by `Provable`.

Separately, a two-sided oracle variant is provided for clarity of the “choice of side”:
for a fixed code `e`, an explicit witness `OraclePick` selects either `encode_halt e` or `encode_not_halt e`
(without any decidability assumption), and yields a local one-step sound extension `S2 ∪ {pick.p}`.


## Explicit Kit Dependency (Types)

```

S : ImpossibleSystem Code PropT
S.K : RHKit
S.h_canon : DetectsMonotone S.K
Rev0_K S.K : Trace → Prop

```
-/

namespace RevHalt

-- ==============================================================================================
-- T3: Complementarity — Explicit Definitions
-- ==============================================================================================

/-- Explicit Kit extraction with visible `RHKit` type. -/
def KitOf {Code PropT : Type} (S : ImpossibleSystem Code PropT) : RHKit := S.K

/-- **S₁** := Non-internalizable set.

`p ∈ S1Set` iff `p = encode_halt e` for some `e` with Kit-certified halting and unprovable.
The Kit is written explicitly as `KitOf S : RHKit`.
-/
def S1Set {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) : Set PropT :=
  { p | ∃ e : Code,
      p = encode_halt e ∧
      Rev0_K (KitOf S) (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) }

/-- **S₃** := S₂ ∪ S₁ (complementary system). -/
def S3Set {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (S2 : Set PropT) (encode_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1Set S encode_halt

/-- Membership lemma: given witness (hKit, hUnprov), `encode_halt e ∈ S₁`. -/
lemma mem_S1Set_of_witness
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    encode_halt e ∈ S1Set S encode_halt := by
  have hEq : KitOf S = S.K := rfl
  have hKit' : Rev0_K (KitOf S) (S.Machine e) := by
    rw [hEq]
    exact hKit
  exact Exists.intro e (And.intro rfl (And.intro hKit' hUnprov))

/-- **S₁ ≠ ∅** given a witness (e, hKit, hUnprov). -/
theorem S1Set_nonempty_of_witness
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT)
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    (S1Set S encode_halt).Nonempty := by
  exact Exists.intro (encode_halt e) (mem_S1Set_of_witness S encode_halt e hKit hUnprov)

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
  refine Exists.intro e ?_
  intro hProv
  have hReal : Rev0_K S.K (S.Machine e) :=
    h_truth_to_real e (h_sound (encode_halt e) hProv)
  have hProvNot : S.Provable (S.Not (encode_halt e)) :=
    he.mp hReal
  exact S.consistent (S.absurd (encode_halt e) hProv hProvNot)

-- ==============================================================================================
-- T3.1 (Weak) — S₃ = S₁ ∪ S₂ is Sound
-- ==============================================================================================

/--
**T3.1 — S₃ = S₁ ∪ S₂ is Sound** (explicit, no `simp`, no `simpa`, no `classical`).
-/
theorem T3_weak_extension_explicit
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    ∃ S3 : Set PropT,
      S3 = S3Set S S2 encode_halt ∧
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      encode_halt e ∈ S1Set S encode_halt ∧
      encode_halt e ∈ S3 ∧
      Halts (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) := by
  let S3 : Set PropT := S3Set S S2 encode_halt

  have hHalt : Halts (S.Machine e) :=
    (T1_traces S.K S.h_canon (S.Machine e)).1 hKit

  have h_mem_S1 : encode_halt e ∈ S1Set S encode_halt :=
    mem_S1Set_of_witness S encode_halt e hKit hUnprov

  refine Exists.intro S3 ?_
  refine And.intro rfl ?_
  refine And.intro ?_ ?_

  · -- S2 ⊆ S3
    intro p hp
    -- S3 = S3Set ... = S2 ∪ S1Set ...
    exact Or.inl hp

  · refine And.intro ?_ ?_
    · -- soundness of S3
      intro p hp
      cases hp with
      | inl hp2 =>
          exact h_S2_sound p hp2
      | inr hp1 =>
          -- hp1 : p ∈ S1Set ...
          rcases hp1 with ⟨e', hpEq, hKit', _hUnprov'⟩
          have hEqK : S.K = KitOf S := Eq.symm rfl
          have hKit'' : Rev0_K S.K (S.Machine e') := by
            rw [hEqK]
            exact hKit'
          have hTrue : Truth (encode_halt e') := h_encode_correct e' hKit''
          rw [hpEq]
          exact hTrue

    · refine And.intro h_mem_S1 ?_
      · refine And.intro ?_ ?_
        · -- encode_halt e ∈ S3
          exact Or.inr h_mem_S1
        · refine And.intro hHalt hUnprov

-- ==============================================================================================
-- Infinite S₁ Elements (indexed witnesses: kit + unprovable)
-- ==============================================================================================

/--
  **Infinite S₁ elements** (indexed witnesses, no injectivity required).

  Captures infinitely many codes with:
  - Kit-certified: `kit i : Rev0_K S.K (Machine (family i))`
  - Non-internalizable: `unprovable i : ¬ S.Provable (encode_halt (family i))`
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
  have hEq : KitOf S = S.K := rfl
  have hKit' : Rev0_K (KitOf S) (S.Machine (I.family i)) := by
    rw [hEq]
    exact I.kit i
  exact Exists.intro (I.family i)
    (And.intro rfl (And.intro hKit' (I.unprovable i)))

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

No `simp`, no `simpa`, no `classical`, no `noncomputable`.
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
  let S3_family : ℕ → Set PropT := fun n =>
    S2 ∪ { p | ∃ i ∈ partition.Parts n, p = encode_halt (indep.family i) }

  refine Exists.intro S3_family ?_
  refine And.intro ?_ (And.intro ?_ ?_)

  · -- S2 ⊆ S3_family n
    intro n p hp
    exact Or.inl hp

  · -- soundness
    intro n p hp
    cases hp with
    | inl hp2 =>
        exact h_S2_sound p hp2
    | inr hpNew =>
        rcases hpNew with ⟨i, _hi, hpEq⟩
        rw [hpEq]
        exact h_encode_correct (indep.family i) (indep.kit i)

  · -- disjointness of new parts (index-level)
    intro n m hnm i hi j hj hEq
    have h_disj : Disjoint (partition.Parts n) (partition.Parts m) :=
      partition.disjoint n m hnm
    -- from i = j, move membership across
    have hi' : j ∈ partition.Parts n := by
      rw [hEq] at hi
      exact hi
    have h_inter : j ∈ partition.Parts n ⊓ partition.Parts m := And.intro hi' hj
    -- Disjoint means intersection is empty
    have h_empty : partition.Parts n ⊓ partition.Parts m = ⊥ := (disjoint_iff.mp h_disj)
    rw [h_empty] at h_inter
    exact h_inter

-- ==============================================================================================
-- Two-sided oracle variant (local one-step extension)
-- No `simp`, no `simpa`, no `classical`, no `noncomputable`.
-- ==============================================================================================

/--
An explicit two-sided oracle *witness* for a given code `e`.

It packages a chosen sentence `p : PropT` together with a certificate that `p` matches
the Kit verdict:
- either `Rev0_K ...` and `p = encode_halt e`,
- or `¬ Rev0_K ...` and `p = encode_not_halt e`.

No decidability of `Rev0_K` is assumed or used.
-/
structure OraclePick {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT) (e : Code) where
  p : PropT
  cert :
    (Rev0_K S.K (S.Machine e) ∧ p = encode_halt e) ∨
    (¬ Rev0_K S.K (S.Machine e) ∧ p = encode_not_halt e)

/-- Local S₁ for a fixed oracle pick: a single frontier sentence. -/
def S1OneSet {PropT : Type} (pick_p : PropT) : Set PropT :=
  {pick_p}

/-- Local S₃ = S₂ ∪ S₁ (with S₁ being the singleton chosen by the oracle). -/
def S3OneSet {PropT : Type} (S2 : Set PropT) (pick_p : PropT) : Set PropT :=
  S2 ∪ S1OneSet pick_p

/--
Oracle variant (two-sided) — explicit and constructive.

- `S2 : Set PropT` is the semantics-side corpus, with explicit soundness witness.
- The oracle provides a `pick` choosing *one* sentence based on the Kit verdict (by certificate).
- We extend by adding exactly that sentence, and prove the extension is sound.
- This establishes the soundness of a single oracle step `S2 ∪ {pick.p}`.

This theorem assumes a witness `pick`; it does not define or compute such a pick.

No branching on `Rev0_K` is computed; the branch is carried by `pick.cert`.
-/
theorem T3_oracle_extension_explicit
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, ¬ Rev0_K S.K (S.Machine e) → Truth (encode_not_halt e))
    (e : Code)
    (pick : OraclePick S encode_halt encode_not_halt e)
    (hUnprov : ¬ S.Provable pick.p) :
    ∃ S3 : Set PropT,
      S3 = S3OneSet S2 pick.p ∧
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      pick.p ∈ S3 ∧
      ¬ S.Provable pick.p ∧
      ((Halts (S.Machine e) ∧ pick.p = encode_halt e) ∨
       (¬ Halts (S.Machine e) ∧ pick.p = encode_not_halt e)) := by
  let S3 : Set PropT := S3OneSet S2 pick.p

  have hIff : Rev0_K S.K (S.Machine e) ↔ Halts (S.Machine e) :=
    T1_traces S.K S.h_canon (S.Machine e)

  have hTruthPick : Truth pick.p := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        have hTrue : Truth (encode_halt e) := h_pos e hKit
        rw [hpEq]
        exact hTrue
    | inr h =>
        have hNotKit : ¬ Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        have hTrue : Truth (encode_not_halt e) := h_neg e hNotKit
        rw [hpEq]
        exact hTrue

  have hBranchHalt :
      (Halts (S.Machine e) ∧ pick.p = encode_halt e) ∨
      (¬ Halts (S.Machine e) ∧ pick.p = encode_not_halt e) := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        have hHalt : Halts (S.Machine e) := (hIff).1 hKit
        exact Or.inl (And.intro hHalt hpEq)
    | inr h =>
        have hNotKit : ¬ Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        have hNotHalt : ¬ Halts (S.Machine e) := by
          intro hHalt
          have hKit : Rev0_K S.K (S.Machine e) := (hIff).2 hHalt
          exact hNotKit hKit
        exact Or.inr (And.intro hNotHalt hpEq)

  refine Exists.intro S3 ?_
  refine And.intro rfl ?_
  refine And.intro ?_ ?_

  · -- S2 ⊆ S3
    intro p hp
    -- S3 = S3OneSet ... = S2 ∪ {pick.p}
    exact Or.inl hp

  · refine And.intro ?_ ?_
    · -- Soundness
      intro p hp
      cases hp with
      | inl hp2 =>
          exact h_S2_sound p hp2
      | inr hp1 =>
          -- hp1 : p ∈ {pick.p}
          have hpEq : p = pick.p := hp1
          rw [hpEq]
          exact hTruthPick

    · refine And.intro ?_ ?_
      · -- pick.p ∈ S3
        have hMemSingleton : pick.p ∈ ({pick.p} : Set PropT) := rfl
        exact Or.inr hMemSingleton
      · refine And.intro hUnprov hBranchHalt

/-
  Two-sided oracle (global frontier) — definitions for later globalization (families/partitions).

  These are not used by `T3_oracle_extension_explicit` (which is a local one-step theorem).
-/

/-- S₁(two-sided global): union of oracle-chosen frontier sentences across all codes `e`. -/
def S1TwoSet {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT) : Set PropT :=
  { p | ∃ e : Code, ∃ pick : OraclePick S encode_halt encode_not_halt e,
      p = pick.p ∧ ¬ S.Provable p }

/-- S₃(two-sided global): S₂ ∪ S₁(two-sided). -/
def S3TwoSet {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (S2 : Set PropT) (encode_halt encode_not_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1TwoSet S encode_halt encode_not_halt

/-- Membership lemma: the oracle-chosen sentence is in S₁(two-sided) given unprovability. -/
lemma mem_S1TwoSet_of_pick
    {Code PropT : Type} (S : ImpossibleSystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code) (pick : OraclePick S encode_halt encode_not_halt e)
    (hUnprov : ¬ S.Provable pick.p) :
    pick.p ∈ S1TwoSet S encode_halt encode_not_halt := by
  refine Exists.intro e ?_
  refine Exists.intro pick ?_
  refine And.intro rfl ?_
  exact hUnprov

end RevHalt
