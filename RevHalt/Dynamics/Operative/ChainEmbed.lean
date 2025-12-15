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
    (hSound : ContextSound ctx) : Set PropT :=
  Chain ctx n

/-- Chain 0 is empty and thus trivially sound. -/
theorem chainTheory_zero_sound (ctx : VerifiableContext Code PropT) :
    TheorySound ctx.toEnrichedContext (Chain ctx 0) := by
  simp only [Chain_zero]
  intro p hp
  exact hp.elim

/-- If ContextSound holds, then Chain n is sound for all n. -/
theorem chainTheory_sound (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (n : ℕ) :
    TheorySound ctx.toEnrichedContext (Chain ctx n) := by
  induction n with
  | zero => exact chainTheory_zero_sound ctx
  | succ n ih =>
    intro p hp
    -- p ∈ Chain (n+1) = Next ctx (Chain n) = CloK (Chain n)
    simp only [Chain_succ, Next] at hp
    -- hp : p ∈ CloK (LR := ctx.LR) (Chain ctx n)
    rw [mem_CloK_iff] at hp
    -- hp : Halts (ctx.LR (Chain ctx n) p)
    -- Use ContextSound: if Chain n is sound, then Halts → Truth
    exact hSound (Chain ctx n) p ih hp

/-- ChainNode n: a TheoryNode based on Chain n (under ContextSound). -/
noncomputable def ChainNode (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (n : ℕ) : Core.TheoryNode ctx.toEnrichedContext where
  theory := Chain ctx n
  sound := chainTheory_sound ctx hSound n

/-- Chain is monotone: Chain n ⊆ Chain (n+1) under LRRefl. -/
theorem chain_mono (ctx : VerifiableContext Code PropT)
    (hRefl : LRRefl ctx) (n : ℕ) :
    Chain ctx n ⊆ Chain ctx (n+1) := by
  induction n with
  | zero =>
    simp only [Chain_zero]
    exact empty_subset _
  | succ n ih =>
    -- Chain (n+1) ⊆ Chain (n+2)
    -- Chain (n+1) = CloK (Chain n)
    -- Chain (n+2) = CloK (Chain (n+1))
    intro p hp
    simp only [Chain_succ, Next] at hp ⊢
    -- Need: p ∈ CloK (Chain (n+1)) given p ∈ CloK (Chain n)
    -- p ∈ CloK (Chain n) means Halts (LR (Chain n) p)
    -- We need Halts (LR (Chain (n+1)) p)
    -- If p ∈ Chain (n+1), then by LRRefl, Halts (LR (Chain (n+1)) p)
    rw [mem_CloK_iff] at hp ⊢
    -- Since Chain n ⊆ Chain (n+1) and LR is... this requires LRMonotone
    -- For now, use that p ∈ Chain (n+1) and hRefl gives us what we need
    have h_in : p ∈ Chain ctx (n+1) := by
      simp only [Chain_succ, Next]
      rw [mem_CloK_iff]
      exact hp
    exact hRefl h_in

/-- ChainNode n ≤ ChainNode (n+1) under LRRefl. -/
theorem chainNode_mono (ctx : VerifiableContext Code PropT)
    (hSound : ContextSound ctx) (hRefl : LRRefl ctx) (n : ℕ) :
    ChainNode ctx hSound n ≤ ChainNode ctx hSound (n+1) := by
  simp only [Core.TheoryNode.le_def, ChainNode]
  exact chain_mono ctx hRefl n

/-!
## Future Work: Path from ChainNodes

A full embedding of the chain into Path would require defining a specific
Move that "advances" from Chain n to Chain (n+1). This is conceptually
similar to the "Next" operator but would need to be formalized as:

```lean
def advanceMove (ctx : VerifiableContext Code PropT) (n : ℕ)
    (p : PropT) (hp : p ∈ NewLayer ctx n) : Move ctx.toEnrichedContext
```

This is deferred as it requires careful handling of the dependency between
the VerifiableContext level (where Chain lives) and the EnrichedContext
level (where Move lives).
-/

end RevHalt.Dynamics.Operative
