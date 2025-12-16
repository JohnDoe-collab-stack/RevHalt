# RevHalt.Dynamics

**Axiom Dynamics**: a calculus for navigating the space of "what proves what."

> This formalizes what [Chen, Li & Oliveira &Igor C. (2024)](https://wrap.warwick.ac.uk/id/eprint/187191/) do intuitively in reverse mathematics — treat provability relationships as a graph you can walk, with every step machine-checked.

## Overview

This module provides a framework for navigating an **axiom graph** where:
- **Nodes** are sound theories (bundled with soundness certificates)
- **Edges** are moves (operations that extend theories)
- **Paths** are sequences of moves between nodes

The framework guarantees soundness without assuming global truth, using **Rev** as a transversal operative invariant.

## The Key Insight: T2 as Fuel

```lean
theorem fuel_from_T2 (T : TheoryNode ctx) (hT : T.theory ⊆ ProvableSet ctx) :
    ∃ m : Move ctx, T < Move.apply m T
```

**T2 is not just an impossibility theorem — it's a fuel generator.** From any node inside ProvableSet, there always exists a strict move forward. This transforms Gödel's incompleteness from a negative result into a positive navigation principle.

## Fork: Bifurcation Without Global Choice

The most elegant structure in the module:

```lean
structure Fork (ctx : EnrichedContext) (T0 : TheoryNode ctx) where
  pivot : PropT
  mkLeft : ctx.Truth pivot → TheoryNode
  mkRight : ctx.Truth (ctx.Not pivot) → TheoryNode
  exclusion : ¬ (TheorySound (Extend T0 pivot) ∧ TheorySound (Extend T0 (Not pivot)))
```

**Fork captures indetermination without resolving it:**
- You don't choose which branch is true
- You have two *conditional* constructors
- The `exclusion` law is a *theorem*, not an assumption
- Fork integrates natively with Graph/Path via `ofPivot_edge_left/right`

## Chain-Dynamics Bridge: Parallel with Real Analysis

The `Operative/` layer establishes a formal parallel between Dynamics and Real Analysis:

| Real Analysis | RevHalt Dynamics |
|---------------|------------------|
| Increasing sequence (uₙ) | `InfiniteNodeChain` (sequence of Moves) |
| uₙ₊₁ ≥ uₙ (monotonicity) | `Move.apply_le` (monotone moves) |
| sup(uₙ) = L (limit) | `ChainLimit = ⋃ theories` |
| ∀ε, ∃N, uₙ ∈ B(L,ε) | `finite_coverage` (ε-δ convergence) |

Key theorems:
- `advanceMove`: Converts `p ∈ Chain(n+1)` to a valid `Move` via `Chain_truth`
- `layer_finite_coverability`: Any finite subset of Chain(n+1) is reachable
- `stratChain_limit_eq_masterClo`: **Limit = MasterClo** (the convergence theorem)

## Concrete Example: OmegaChaitin

`OmegaChaitin.lean` is the proof that Dynamics works on a real computability domain:

| Dynamics (abstract) | OmegaChaitin (concrete) |
|---------------------|-------------------------|
| T2 = fuel | `TrueCuts` is RE — can always advance |
| Fork = bifurcation | Bit = 0 or 1, undecidable which |
| Move.apply preserves soundness | `OmegaApprox_mono` |
| Gap = true but unprovable | Individual bits of Ω |

## Kolmogorov Emergence

`OmegaComplexity.lean` establishes that Kolmogorov complexity **emerges** from Dynamics:

```lean
theorem stable_bits_bounded_by_time (t : ℕ) : stableBits t ≤ t
```

**Key insight**: OmegaApprox t has resolution 2^{-t}. To determine n bits stably, we need t ≥ n.

| Classical (Chaitin) | Dynamics |
|---------------------|----------|
| K(Ω_n) ≥ n - O(1) | stableBits(t) ≤ t |
| Ω is incompressible | Each step gives ≤ 1 bit |

The connection is **meta-theoretic**: both express that Ω is maximally complex.

## Architecture

```
Dynamics/
├── Core/               ← EnrichedContext level
│   ├── Node.lean       ← TheoryNode = (theory, soundness)
│   ├── Move.lean       ← Move inductive (extend, extend_gap)
│   ├── Laws.lean       ← Preservation, Strictness, Bifurcation
│   ├── Fuel.lean       ← T2 guarantees strict moves exist
│   ├── Graph.lean      ← Edge relation, Reachability
│   ├── Path.lean       ← Path inductive (general)
│   ├── Fork.lean       ← Bifurcation as object
│   └── RefSystem.lean  ← Cut/Bit encoding framework
├── Operative/          ← VerifiableContext level
│   ├── Invariant.lean  ← RevLabel (operative invariant)
│   ├── ChainEmbed.lean ← Chain → Move/Path bridge (advanceMove, layer_finite_coverability)
│   └── Limit.lean      ← InfiniteNodeChain, ChainLimit = MasterClo (ε-δ convergence)
├── Instances/          ← Concrete instances
│   ├── OmegaChaitin.lean    ← Chaitin's Ω as RefSystem instance (computable)
│   └── OmegaComplexity.lean ← Precision/complexity analysis for Ω
├── Transport/          ← Inter-graph morphisms
│   └── Morphism.lean   ← TheoryMorphism (functorial)
└── System.lean         ← Unified bundle
```

## Laws

| Law | Meaning |
|-----|---------|
| **Preservation** | `apply` always produces sound nodes |
| **Strictness** | Fresh extensions are strictly larger |
| **Bifurcation** | No sound node contains both `p` and `Not p` |

## Design Principles

1. **Two-layer separation**: Core (pure set-theoretic) vs Operative (with LR/Halts/Rev)
2. **Monotone moves only**: No `restrict` operation (avoids complexity)
3. **Path ≠ Chain**: Path is general; Chain embeds as special case via `ChainEmbed`
4. **Transport is functorial**: Maps between graphs, not within
5. **Limit = MasterClo**: The limit of the canonical chain equals the kinetic closure

## Validation

```bash
lake build RevHalt.Dynamics.System
lake build RevHalt.Dynamics.Core.Fork
lake build RevHalt.Dynamics.Core.RefSystem
lake build RevHalt.Dynamics.Operative.Limit
lake build RevHalt.Dynamics.Instances.OmegaChaitin
lake build RevHalt.Dynamics.Instances.OmegaComplexity
```
