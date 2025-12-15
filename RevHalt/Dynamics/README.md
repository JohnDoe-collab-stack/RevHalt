# RevHalt.Dynamics

Axiom Dynamics: a calculus for manipulating local theories within a graph structure.

## Overview

This module provides a framework for navigating an **axiom graph** where:
- **Nodes** are sound theories (bundled with soundness certificates)
- **Edges** are moves (operations that extend theories)
- **Paths** are sequences of moves between nodes

The framework guarantees soundness without assuming global truth, using **Rev** as a transversal operative invariant.

## Architecture

```
Dynamics/
├── Core/           ← EnrichedContext level
│   ├── Node.lean   ← TheoryNode = (theory, soundness)
│   ├── Move.lean   ← Move inductive (extend, extend_gap)
│   ├── Laws.lean   ← Preservation, Strictness, Bifurcation
│   ├── Fuel.lean   ← T2 guarantees strict moves exist
│   ├── Graph.lean  ← Edge relation, Reachability
│   └── Path.lean   ← Path inductive (general)
├── Operative/      ← VerifiableContext level
│   ├── Invariant.lean  ← RevLabel (operative invariant)
│   └── ChainEmbed.lean ← Chain → Path relationship
├── Transport/      ← Inter-graph morphisms
│   └── Morphism.lean   ← TheoryMorphism (functorial)
└── System.lean     ← Unified bundle
```

## Key Concepts

### Core Layer (EnrichedContext)

| Concept | Definition |
|---------|------------|
| `TheoryNode` | Σ-type `(theory : Set PropT, sound : TheorySound ctx theory)` |
| `Move` | `extend p hp \| extend_gap w` (monotone operations) |
| `Move.apply` | Total function `Move → Node → Node` |
| `Edge` | Exists a move connecting two nodes |
| `Path` | Inductive sequence of moves |

### Laws

| Law | Meaning |
|-----|---------|
| **Preservation** | `apply` always produces sound nodes |
| **Strictness** | Fresh extensions are strictly larger |
| **Bifurcation** | No sound node contains both `p` and `Not p` |

### Fuel (T2)

```lean
theorem fuel_from_T2 (T : TheoryNode ctx) (hT : T.theory ⊆ ProvableSet ctx) :
    ∃ m : Move ctx, T < Move.apply m T
```

T2 guarantees that from any node inside ProvableSet, a strict move exists.

### Operative Layer (VerifiableContext)

**RevLabel (Invariant.lean):**
```lean
def RevLabel (ctx : VerifiableContext Code PropT) (p : PropT) : Prop :=
  Halts (ctx.LR ∅ p)
```

RevLabel is kit-invariant and equals Truth via the bridge.

**ChainEmbed (ChainEmbed.lean):**
```lean
def ChainNode (ctx : VerifiableContext) (hSound : ContextSound ctx) (n : ℕ) :
    TheoryNode ctx.toEnrichedContext
```

Provides the bridge between Stratification's `Chain n` and Dynamics' `TheoryNode`.

### Transport Layer

```lean
structure TheoryMorphism (ctx₁ ctx₂ : EnrichedContext) where
  map : PropT₁ → PropT₂
  preserves_truth : ∀ p, ctx₁.Truth p → ctx₂.Truth (map p)
  preserves_not : ∀ p, map (ctx₁.Not p) = ctx₂.Not (map p)
```

Transport is **functorial** (between graphs), not an internal move.

## Usage

```lean
import RevHalt.Dynamics.System

-- Core dynamics at EnrichedContext level
def myDynamics : AxiomDynamicsCore Code PropT := { ctx := myContext }

-- Operative dynamics with Rev invariant
def myOpDynamics : AxiomDynamicsOperative Code PropT := {
  ctx := myContext.toEnrichedContext,
  vctx := myVerifiableContext,
  h_compat := rfl
}
```

## Design Principles

1. **Two-layer separation**: Core (pure set-theoretic) vs Operative (with LR/Halts/Rev)
2. **Monotone moves only**: No `restrict` operation (avoids complexity)
3. **Path ≠ Chain**: Path is general; Chain embeds as special case
4. **Transport is functorial**: Maps between graphs, not within

## Dependencies

- `RevHalt.Bridge.Context` (EnrichedContext, GapWitness)
- `RevHalt.Bridge.ComplementarityAPI` (TheorySound, Extend)
- `RevHalt.Kinetic.MasterClosure` (VerifiableContext)
- `RevHalt.Kinetic.Stratification` (Chain, ContextSound)
- `RevHalt.Kinetic.System` (GapTruth)

## Validation

```bash
lake build RevHalt.Dynamics.System
lake build RevHalt.Dynamics.Operative.ChainEmbed
```
