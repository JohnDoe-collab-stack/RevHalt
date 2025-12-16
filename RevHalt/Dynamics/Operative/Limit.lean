/-
  RevHalt.Dynamics.Operative.Limit

  Limit Theorem: The Dynamics converges to MasterClo.

  ## Parallel with Real Analysis

  | Analysis | RevHalt |
  |----------|---------|
  | Increasing sequence (uₙ) | InfiniteChain (sequence of Moves) |
  | uₙ₊₁ ≥ uₙ | Move.apply_le (monotonicity) |
  | sup(uₙ) = L | ChainLimit = ⋃ theories |
  | ∀ε, ∃N, uₙ ∈ B(L,ε) | finite_coverage (ε-δ) |

  This file establishes the formal link between finite coverage
  (layer_finite_coverability) and convergence to MasterClo.
-/

import RevHalt.Dynamics.Operative.ChainEmbed
import RevHalt.Kinetic.Stratification

namespace RevHalt.Dynamics.Operative.Limit

open Set RevHalt RevHalt.Kinetic RevHalt.Dynamics.Core

/-!
## 1. Infinite Node Chains

An "infinite chain" is a function ℕ → TheoryNode where each
transition preserves monotonicity (T_n ⊆ T_{n+1}).
-/

/-- InfiniteNodeChain: increasing sequence of TheoryNodes. -/
structure InfiniteNodeChain {Code PropT : Type} (ctx : EnrichedContext Code PropT) where
  /-- The sequence of nodes indexed by ℕ. -/
  node : ℕ → TheoryNode ctx
  /-- Monotonicity: each node is contained in the next. -/
  mono : ∀ n, node n ≤ node (n + 1)

namespace InfiniteNodeChain

variable {Code PropT : Type} {ctx : EnrichedContext Code PropT}

/-- Transitive monotonicity: node m ≤ node n for m ≤ n. -/
theorem mono_le (chain : InfiniteNodeChain ctx) {m n : ℕ} (h : m ≤ n) :
    chain.node m ≤ chain.node n := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at h
    rw [h]
    exact TheoryNode.node_le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
      exact TheoryNode.node_le_trans (ih hle) (chain.mono n)
    · rw [heq]
      exact TheoryNode.node_le_refl _

end InfiniteNodeChain

/-!
## 2. Chain Limit

The limit is the directed union of all theories along the chain.
-/

variable {Code PropT : Type} {ctx : EnrichedContext Code PropT}

/-- ChainLimit: the union of all theories in the chain. -/
def ChainLimit (chain : InfiniteNodeChain ctx) : Set PropT :=
  ⋃ n, (chain.node n).theory

/-- Membership in limit: p ∈ ChainLimit ↔ ∃ n, p ∈ node(n). -/
theorem mem_chainLimit_iff (chain : InfiniteNodeChain ctx) (p : PropT) :
    p ∈ ChainLimit chain ↔ ∃ n, p ∈ (chain.node n).theory := by
  simp only [ChainLimit, Set.mem_iUnion]

/-- The limit is monotone with respect to the starting chain. -/
theorem chainLimit_mono (chain : InfiniteNodeChain ctx) (n : ℕ) :
    (chain.node n).theory ⊆ ChainLimit chain := by
  intro p hp
  rw [mem_chainLimit_iff]
  exact ⟨n, hp⟩

/-!
## 3. Finite Coverage (ε-δ)

For any finite subset of the limit, there exists a level n
such that this subset is contained in node(n).

This is the analogue of ε-δ convergence: for any finite "tolerance",
we can find a point in the sequence that satisfies it.
-/

/-- Finite coverage: any finite subset of the limit is reached. -/
theorem finite_coverage [DecidableEq PropT] (chain : InfiniteNodeChain ctx) :
    ∀ S : Finset PropT, (∀ p ∈ S, p ∈ ChainLimit chain) →
      ∃ n, ∀ p ∈ S, p ∈ (chain.node n).theory := by
  intro S hS
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun p hp => (Finset.notMem_empty p hp).elim⟩
  | insert a S' ha ih =>
    have ha_limit : a ∈ ChainLimit chain := hS a (Finset.mem_insert_self a S')
    rw [mem_chainLimit_iff] at ha_limit
    obtain ⟨n_a, hna⟩ := ha_limit
    have hS'_limit : ∀ p ∈ S', p ∈ ChainLimit chain :=
      fun p hp => hS p (Finset.mem_insert_of_mem hp)
    obtain ⟨n_S', hnS'⟩ := ih hS'_limit
    use max n_a n_S'
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact chain.mono_le (Nat.le_max_left n_a n_S') hna
    · exact chain.mono_le (Nat.le_max_right n_a n_S') (hnS' p hp')

/-!
## 4. Link with Stratification Chain

If an InfiniteNodeChain is built from the ChainNodes
of the stratification, then its limit coincides with MasterClo.
-/

/-- StratChain: the canonical chain built from Chain n. -/
def StratChain (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (hRefl : LRRefl ctx) : InfiniteNodeChain ctx.toEnrichedContext where
  node := fun n => ChainNode ctx hSound n
  mono := fun n => chainNode_mono ctx hSound hRefl n

/-- The limit of StratChain is exactly MasterClo. -/
theorem stratChain_limit_eq_masterClo (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (hRefl : LRRefl ctx) :
    ChainLimit (StratChain ctx hSound hRefl) = MasterClo ctx := by
  ext p
  rw [mem_chainLimit_iff, mem_MasterClo_iff]
  constructor
  · intro ⟨n, hn⟩
    use n
    simp only [StratChain, ChainNode] at hn
    exact hn
  · intro ⟨n, hn⟩
    use n
    simp only [StratChain, ChainNode]
    exact hn

/-!
## 5. Main Theorem: Coverage ↔ Convergence to MasterClo
-/

/-- Convergence theorem: for any Finset S ⊆ MasterClo,
    there exists a level n such that S is covered by Chain n. -/
theorem masterClo_finite_coverage [DecidableEq PropT]
    (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (hRefl : LRRefl ctx)
    (S : Finset PropT)
    (hS : ∀ p ∈ S, p ∈ MasterClo ctx) :
    ∃ n, ∀ p ∈ S, p ∈ Chain ctx n := by
  have hLimit : ∀ p ∈ S, p ∈ ChainLimit (StratChain ctx hSound hRefl) := by
    intro p hp
    rw [stratChain_limit_eq_masterClo]
    exact hS p hp
  obtain ⟨n, hn⟩ := finite_coverage (StratChain ctx hSound hRefl) S hLimit
  use n
  intro p hp
  simp only [StratChain, ChainNode] at hn
  exact hn p hp

/-- Corollary: MasterClo is the directed union of Chain n. -/
theorem masterClo_is_directed_limit (ctx : VerifiableContext Code PropT) :
    MasterClo ctx = ⋃ n, Chain ctx n := by
  ext p
  rw [mem_MasterClo_iff, Set.mem_iUnion]

end RevHalt.Dynamics.Operative.Limit
