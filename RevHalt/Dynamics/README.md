# RevHalt.Dynamics

**Axiom Dynamics**: a calculus for navigating the space of "what proves what."

> This formalizes what Chen, Li & Oliveira do intuitively in reverse mathematics — treat provability relationships as a graph you can walk, with every step machine-checked.

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

## Concrete Example: OmegaChaitin

`OmegaChaitin.lean` is the proof that Dynamics works on a real computability domain:

| Dynamics (abstract) | OmegaChaitin (concrete) |
|---------------------|-------------------------|
| T2 = fuel | `TrueCuts` is RE — can always advance |
| Fork = bifurcation | Bit = 0 or 1, undecidable which |
| Move.apply preserves soundness | `OmegaApprox_mono` |
| Gap = true but unprovable | Individual bits of Ω |

## Architecture

```
Dynamics/
├── Core/           ← EnrichedContext level
│   ├── Node.lean   ← TheoryNode = (theory, soundness)
│   ├── Move.lean   ← Move inductive (extend, extend_gap)
│   ├── Laws.lean   ← Preservation, Strictness, Bifurcation
│   ├── Fuel.lean   ← T2 guarantees strict moves exist
│   ├── Graph.lean  ← Edge relation, Reachability
│   ├── Path.lean   ← Path inductive (general)
│   └── Fork.lean   ← Bifurcation as object
├── Operative/      ← VerifiableContext level
│   ├── Invariant.lean  ← RevLabel (operative invariant)
│   └── ChainEmbed.lean ← Chain → Path relationship
├── Transport/      ← Inter-graph morphisms
│   └── Morphism.lean   ← TheoryMorphism (functorial)
└── System.lean     ← Unified bundle
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
3. **Path ≠ Chain**: Path is general; Chain embeds as special case
4. **Transport is functorial**: Maps between graphs, not within

## Validation

```bash
lake build RevHalt.Dynamics.System
lake build RevHalt.Dynamics.Core.Fork
```

