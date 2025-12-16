/-
  RevHalt.Dynamics.Operative.ChainEmbed

  Relationship between Stratification Chain and Dynamics Path.

  Note: Chain (from Stratification) is a different concept from Path:
  - Chain n : ℕ → Set PropT (iterative closure of CloK)
  - Path : explicit sequence of Moves between TheoryNodes

  This module provides the conceptual bridge.
-/

import RevHalt.Dynamics.Core.Path
import RevHalt.Kinetic.Stratification
import Mathlib.Data.Finset.Basic

namespace RevHalt.Dynamics.Operative

open Set RevHalt RevHalt.Kinetic

variable {Code PropT : Type}

/-!
## Conceptual Relationship

The **Chain** from Stratification and **Path** from Dynamics are related but distinct:

1. **Chain n** represents the nth iteration of the CloK operator on sets:
   - Chain 0 = ∅
   - Chain (n+1) = CloK(Chain n)

2. **Path** represents a sequence of theory-extending moves:
   - Path.nil : T → T (identity)
   - Path.step : extend by one move

The connection is that each stage of Chain corresponds to a "layer" of truths
that become accessible. A Path that extends a theory by propositions from
successive Chain levels can be seen as "following the chain".
-/

/-- A node based on Chain n: the theory is Chain n, soundness from ContextSound. -/
def ChainTheory (ctx : VerifiableContext Code PropT) (n : ℕ)
    (_hSound : ContextSound ctx) : Set PropT :=
  Chain ctx n

/-- Chain 0 is empty and thus trivially sound. -/
theorem chainTheory_zero_sound (ctx : VerifiableContext Code PropT) :
    TheorySound ctx.toEnrichedContext (Chain ctx 0) := by
  simp only [Chain_zero]
  intro p hp
  exact hp.elim

/-- If ContextSound holds, then Chain n is sound for all n.
    (Alias to Kinetic.Chain_truth) -/
theorem chainTheory_sound (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (n : ℕ) :
    TheorySound ctx.toEnrichedContext (Chain ctx n) :=
  fun p hp => Chain_truth ctx hSound n p hp

/-- ChainNode n: a TheoryNode based on Chain n (under ContextSound). -/
def ChainNode (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (n : ℕ) : Core.TheoryNode ctx.toEnrichedContext where
  theory := Chain ctx n
  sound := chainTheory_sound ctx hSound n

/-- Chain is monotone: Chain n ⊆ Chain (n+1) under LRRefl.
    (Alias to Kinetic.Chain_mono_succ) -/
theorem chain_mono (ctx : VerifiableContext Code PropT)
    (hRefl : LRRefl ctx) (n : ℕ) :
    Chain ctx n ⊆ Chain ctx (n+1) :=
  Chain_mono_succ ctx hRefl n

/-- ChainNode n ≤ ChainNode (n+1) under LRRefl. -/
theorem chainNode_mono (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (hRefl : LRRefl ctx) (n : ℕ) :
    ChainNode ctx hSound n ≤ ChainNode ctx hSound (n+1) := by
  simp only [Core.TheoryNode.le_def, ChainNode]
  exact chain_mono ctx hRefl n

/-!
## Bridge: Chain → Move (Computable)

The key insight: `Chain_truth` converts a proof `hp : p ∈ Chain ctx (n+1)`
into a truth certificate `ctx.Truth p`. This certificate is exactly what
`Move.extend` needs. No `Classical.choice` is required.
-/

/-- **advanceMove**: Convert Chain(n+1) membership to a valid Move.
    Computable: uses `Chain_truth` to produce the truth certificate. -/
def advanceMove (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (p : PropT)
    (hp : p ∈ Chain ctx (n + 1)) : Core.Move ctx.toEnrichedContext :=
  Core.Move.extend p (Chain_truth ctx hSound (n + 1) p hp)

/-- advanceMove always extends the starting node. -/
theorem advanceMove_extends_chain (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (p : PropT)
    (hp : p ∈ Chain ctx (n + 1))
    (startNode : Core.TheoryNode ctx.toEnrichedContext) :
    startNode ≤ Core.Move.apply (advanceMove ctx hSound n p hp) startNode :=
  Core.Move.apply_le (advanceMove ctx hSound n p hp) startNode

/-- Single-step path from advanceMove (generic startNode). -/
def advancePath (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (startNode : Core.TheoryNode ctx.toEnrichedContext)
    (p : PropT)
    (hp : p ∈ Chain ctx (n + 1)) :
    Core.Path ctx.toEnrichedContext startNode
      (Core.Move.apply (advanceMove ctx hSound n p hp) startNode) :=
  Core.Path.of_move (advanceMove ctx hSound n p hp) startNode

/-!
## Covering: Absorbing Multiple Propositions (Computable)

Since Chain(n+1) can be infinite, we construct paths that absorb finite lists.
-/

/-- **advancePathList**: Recursively absorb a list of propositions from Chain(n+1).
    Computable: recursive on `List`, constructs explicit paths. -/
def advancePathList (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (startNode : Core.TheoryNode ctx.toEnrichedContext)
    (ps : List PropT)
    (h_subset : ∀ p, p ∈ ps → p ∈ Chain ctx (n + 1)) :
    Σ (endNode : Core.TheoryNode ctx.toEnrichedContext),
      Core.Path ctx.toEnrichedContext startNode endNode :=
  match ps with
  | [] => ⟨startNode, Core.Path.nil startNode⟩
  | p :: rest =>
    let ⟨midNode, pathPrefix⟩ := advancePathList ctx hSound n startNode rest
      (fun q hq => h_subset q (List.mem_cons_of_mem p hq))
    have hp : p ∈ Chain ctx (n + 1) := h_subset p (by simp)
    let move := advanceMove ctx hSound n p hp
    let finalNode := Core.Move.apply move midNode
    let pathSuffix := Core.Path.of_move move midNode
    ⟨finalNode, Core.Path.concat pathPrefix pathSuffix⟩

/-- The endNode of advancePathList contains all propositions from the list. -/
theorem path_covers_list (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (startNode : Core.TheoryNode ctx.toEnrichedContext)
    (ps : List PropT)
    (h_subset : ∀ p, p ∈ ps → p ∈ Chain ctx (n + 1)) :
    ∀ p ∈ ps, p ∈ (advancePathList ctx hSound n startNode ps h_subset).1 := by
  induction ps generalizing startNode with
  | nil => intro p hp; contradiction
  | cons head tail ih =>
    intro p hp
    simp only [advancePathList]
    rcases List.mem_cons.mp hp with rfl | h_in_tail
    · -- p = head
      exact Core.Move.prop_mem_apply _ _
    · -- p ∈ tail
      have tail_subset : ∀ q, q ∈ tail → q ∈ Chain ctx (n + 1) :=
        fun q hq => h_subset q (List.mem_cons_of_mem head hq)
      have h_in_mid := ih startNode tail_subset p h_in_tail
      exact Core.Move.apply_le _ _ h_in_mid

/-- **layer_finite_coverability**: Any finite subset of Chain(n+1) is reachable. -/
theorem layer_finite_coverability (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx)
    (n : ℕ)
    (S : Finset PropT)
    (hS : ∀ p ∈ S, p ∈ Chain ctx (n + 1)) :
    ∃ (T : Core.TheoryNode ctx.toEnrichedContext)
      (_path : Core.Path ctx.toEnrichedContext (ChainNode ctx hSound n) T),
      ∀ p ∈ S, p ∈ T := by
  have h_list : ∀ p, p ∈ S.toList → p ∈ Chain ctx (n + 1) := by
    intro p hp; exact hS p (Finset.mem_toList.mp hp)
  let result := advancePathList ctx hSound n (ChainNode ctx hSound n) S.toList h_list
  exact ⟨result.1, result.2, fun p hp =>
    path_covers_list ctx hSound n (ChainNode ctx hSound n) S.toList h_list p
      (Finset.mem_toList.mpr hp)⟩

end RevHalt.Dynamics.Operative
