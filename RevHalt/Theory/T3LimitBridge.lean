/-
  RevHalt.Theory.T3LimitBridge

  Bridge theorem: T3 frontier (InfiniteS1) → Dynamics limit (InfiniteNodeChain)

  ## Core Insight

  | T3 (Complementarity) | Limit (Dynamics) |
  |----------------------|------------------|
  | InfiniteS1.family : Index → Code | Cumulative chain of theories |
  | S3_family n : Set PropT | TheoryNode.theory n |
  | Partition.Parts n | Cumulative frontier at level n |

  The bridge shows that an infinite family of S₁ witnesses
  can be organized into a monotone chain of TheoryNodes.
-/

import RevHalt.Theory.Complementarity
import RevHalt.Dynamics.Operative.Limit

namespace RevHalt.Theory.T3LimitBridge

open Set RevHalt RevHalt.Dynamics.Core RevHalt.Dynamics.Operative.Limit

/-!
## 1. Cumulative Partition

A cumulative partition is a sequence of sets where each level
includes all previous levels: Parts n ⊆ Parts (n+1).
-/

/-- CumulativePartition: Parts form an increasing sequence. -/
structure CumulativePartition (Index : Type) where
  Parts : ℕ → Set Index
  cumulative : ∀ n, Parts n ⊆ Parts (n + 1)

namespace CumulativePartition

variable {Index : Type}

/-- Transitivity: Parts m ⊆ Parts n for m ≤ n. -/
theorem parts_mono (P : CumulativePartition Index) {m n : ℕ} (h : m ≤ n) :
    P.Parts m ⊆ P.Parts n := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at h
    rw [h]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
      exact fun i hi => P.cumulative n (ih hle hi)
    · rw [heq]

/-- Canonical cumulative partition: Parts n = {0, 1, ..., n-1} -/
def canonical : CumulativePartition ℕ where
  Parts := fun n => { i | i < n }
  cumulative := fun _ _ hi => Nat.lt_succ_of_lt hi

/-- The canonical partition at level n+1 contains n. -/
theorem canonical_mem_succ (n : ℕ) : n ∈ canonical.Parts (n + 1) := by
  simp only [canonical, Set.mem_setOf_eq]
  exact Nat.lt_succ_self n

end CumulativePartition

/-!
## 2. Theory from S1 Witnesses

Given an infinite family of witnesses and a cumulative partition,
we can build a family of theories indexed by ℕ.
-/

variable {Code PropT : Type}

/-- Theory at level n: S2 ∪ { encode_halt(family i) | i ∈ Parts n }. -/
def theoryAtLevel
    (S2 : Set PropT)
    (encode_halt : Code → PropT)
    (family : ℕ → Code)
    (P : CumulativePartition ℕ)
    (n : ℕ) : Set PropT :=
  S2 ∪ { p | ∃ i ∈ P.Parts n, p = encode_halt (family i) }

/-- Monotonicity: theory at level n ⊆ theory at level (n+1). -/
theorem theoryAtLevel_mono
    (S2 : Set PropT)
    (encode_halt : Code → PropT)
    (family : ℕ → Code)
    (P : CumulativePartition ℕ)
    (n : ℕ) :
    theoryAtLevel S2 encode_halt family P n ⊆
    theoryAtLevel S2 encode_halt family P (n + 1) := by
  intro p hp
  cases hp with
  | inl hS2 => exact Or.inl hS2
  | inr hNew =>
    right
    obtain ⟨i, hi, hpEq⟩ := hNew
    exact ⟨i, P.cumulative n hi, hpEq⟩

/-!
## 3. Main Bridge Theorem (Abstract)

This is the abstract statement connecting T3 structure to chain structure.
The key observation is that InfiniteS1 provides:
- Infinitely many witnesses (family)
- Each witness is kit-certified and unprovable

These can be organized into a monotone chain via a cumulative partition.
-/

/-- Soundness of theoryAtLevel given S2 soundness and encoding correctness. -/
theorem theoryAtLevel_sound
    (ctx : EnrichedContext Code PropT)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, ctx.Truth p)
    (encode_halt : Code → PropT)
    (family : ℕ → Code)
    (h_family_true : ∀ i, ctx.Truth (encode_halt (family i)))
    (P : CumulativePartition ℕ)
    (n : ℕ) :
    TheorySound ctx (theoryAtLevel S2 encode_halt family P n) := by
  intro p hp
  cases hp with
  | inl hS2 => exact h_S2_sound p hS2
  | inr hNew =>
    obtain ⟨i, _, hpEq⟩ := hNew
    rw [hpEq]
    exact h_family_true i

/--
**Main Bridge Theorem**: A family of witnesses generates a monotone chain.

Given:
- An EnrichedContext
- A base theory S2 (sound)
- A witness family (with truth certificates)

Produces:
- A monotone chain where node(n).theory = theoryAtLevel n
-/
theorem T3_generates_chain
    (ctx : EnrichedContext Code PropT)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, ctx.Truth p)
    (encode_halt : Code → PropT)
    (family : ℕ → Code)
    (h_family_true : ∀ i, ctx.Truth (encode_halt (family i)))
    (P : CumulativePartition ℕ) :
    ∃ chain : InfiniteNodeChain ctx,
      (∀ n, (chain.node n).theory = theoryAtLevel S2 encode_halt family P n) := by

  -- Construct the chain
  let mkNode : ℕ → TheoryNode ctx := fun n => {
    theory := theoryAtLevel S2 encode_halt family P n
    sound := theoryAtLevel_sound ctx S2 h_S2_sound encode_halt family h_family_true P n
  }

  let chain : InfiniteNodeChain ctx := {
    node := mkNode
    mono := fun n => theoryAtLevel_mono S2 encode_halt family P n
  }

  exact ⟨chain, fun n => rfl⟩

/-- The limit of such a chain contains all witnesses. -/
theorem chain_limit_contains_all_witnesses
    (ctx : EnrichedContext Code PropT)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, ctx.Truth p)
    (encode_halt : Code → PropT)
    (family : ℕ → Code)
    (h_family_true : ∀ i, ctx.Truth (encode_halt (family i))) :
    let P := CumulativePartition.canonical
    let chain := (T3_generates_chain ctx S2 h_S2_sound encode_halt family h_family_true P).choose
    ∀ i, encode_halt (family i) ∈ ChainLimit chain :=
  fun i =>
    let P := CumulativePartition.canonical
    let h := T3_generates_chain ctx S2 h_S2_sound encode_halt family h_family_true P
    let chain := h.choose
    let hspec := h.choose_spec
    -- Membership in ChainLimit = ∃ n, p ∈ node(n).theory
    -- We witness with n = i + 1
    let hmem_theory : encode_halt (family i) ∈ theoryAtLevel S2 encode_halt family P (i + 1) :=
      Or.inr ⟨i, CumulativePartition.canonical_mem_succ i, rfl⟩
    let hmem_node : encode_halt (family i) ∈ (chain.node (i + 1)).theory :=
      (hspec (i + 1)).symm ▸ hmem_theory
    Set.mem_iUnion.mpr ⟨i + 1, hmem_node⟩

/-!
## 4. Connection: InfiniteS1 provides the witness family

The InfiniteS1 structure from Complementarity.lean provides exactly
what we need for T3_generates_chain.
-/

/--
**Corollary**: InfiniteS1 (from T3) generates a chain converging to S₃.

This is the formal bridge between:
- T3_strong (Theory level): InfiniteS1 → infinite family of S₃ extensions
- Limit.lean (Dynamics level): InfiniteNodeChain → ChainLimit
-/
theorem InfiniteS1_generates_chain
    (ctx : EnrichedContext Code PropT)
    (S : ComplementaritySystem Code PropT)
    (_hCtx : ctx.toComplementaritySystem = S)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, ctx.Truth p)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → ctx.Truth (encode_halt e))
    (indep : InfiniteS1 S encode_halt)
    (enum : ℕ → indep.Index) -- enumeration of the index
    (_h_surj : Function.Surjective enum) :
    ∃ chain : InfiniteNodeChain ctx,
      -- (1) Base is included
      (∀ n, S2 ⊆ (chain.node n).theory) ∧
      -- (2) All witnesses are in the limit
      (∀ i, encode_halt (indep.family (enum i)) ∈ ChainLimit chain) ∧
      -- (3) Each node is sound
      (∀ n, TheorySound ctx (chain.node n).theory) := by
  -- Extract the family as ℕ → Code
  let family : ℕ → Code := fun n => indep.family (enum n)
  let P := CumulativePartition.canonical

  -- All witnesses are true (via kit certification)
  have h_family_true : ∀ i, ctx.Truth (encode_halt (family i)) := by
    intro i
    have hKit : Rev0_K S.K (S.Machine (indep.family (enum i))) := indep.kit (enum i)
    exact h_encode_correct (indep.family (enum i)) hKit

  -- Build the chain
  obtain ⟨chain, hchain⟩ := T3_generates_chain ctx S2 h_S2_sound encode_halt family h_family_true P

  refine ⟨chain, ?_, ?_, ?_⟩

  · -- S2 ⊆ node(n).theory
    intro n p hp
    rw [hchain n]
    exact Or.inl hp

  · -- All witnesses in limit
    intro i
    rw [mem_chainLimit_iff]
    use i + 1
    rw [hchain (i + 1)]
    right
    refine ⟨i, CumulativePartition.canonical_mem_succ i, rfl⟩

  · -- Soundness
    intro n
    exact (chain.node n).sound

end RevHalt.Theory.T3LimitBridge
