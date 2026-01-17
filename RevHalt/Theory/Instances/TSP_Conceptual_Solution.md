# Conceptual solution for TSP in RevHalt

This note explains the conceptual "solution" path in `TSP.lean` and how it
differs from the usual treatment of TSP and P vs NP.

## What "solution" means here

The file does not give a new algorithm for TSP. It gives a formal bridge from:

- a concrete NP problem (TSP),
- to halting and provability dynamics (RevHalt),
- and to a **derived** statement about efficient search.

So the "solution" is a meta-theoretic pipeline: encode, model, relate halting,
then show how certain trajectory constraints **force** a Collapse result
that yields an efficient search procedure.

## Core conceptual steps

1) Computable encodings

- Tours, graphs, and instances are encoded into natural numbers.
- Decoding is constructive, with roundtrip lemmas to show no information is lost.

1) Machine semantics

- A trace enumerates tours and checks validity.
- The key equivalence is: the machine halts iff a valid tour exists.

1) Frontier and trajectory

- `S1Rel_TSP` captures true-but-unprovable halting statements in a theory state.
- Trajectory operators iterate theory enrichment and define an omega limit.
- This sets up the setting for Route II and the trilemma.

1) Route II and the trilemma

- Route II provides conditions under which the frontier is nonempty.
- The trilemma says you cannot keep Absorbable, OmegaAdmissible, and RouteIIAt
  together; one must fail.

1) Canonization and Collapse

- If the frontier is empty, you get positive completeness at omega.
- A separate negative completeness assumption is needed for full canonization.
- To move from "provable halting" to an actual tour, you need extraction.
- An effective canonization bundles decision and extraction as data.
- From that data, Collapse is **derived** as a theorem, not assumed as an axiom.

## Key insight: Collapse is OUTPUT, not INPUT

The Collapse result is **not** an arbitrary axiom added for convenience.
It is the **logical consequence** of the framework's structure:

```
Route II conditions (given by the problem structure)
       ↓
   Trilemma (proven from dynamics)
       ↓
¬RouteIIAt ⟹ S1Rel_TSP = ∅ (frontier empty)
       ↓
PosComplete at ω (positive completeness)
       +
NegComplete (completeness hypothesis)
       ↓
Canonization at ω (full completeness)
       +
Effective extraction (constructive data)
       ↓
  **Collapse**  ← DERIVED OUTPUT
```

What is **assumed**:

- DetectsMono K (structural property of the kernel)
- OmegaAdmissible (trajectory coherence)
- NegComplete (theory completeness)
- Effective extraction (constructive certificate schema)

What is **derived**:

- Trilemma disjunction
- PosComplete from ¬RouteIIAt
- Canonization from PosComplete + NegComplete
- **Collapse** from Canonization + extraction

## What changes vs the usual view

Usual view:

- TSP is NP-complete; P vs NP is a single global question.
- Proofs focus on reductions and algorithmic lower/upper bounds.

RevHalt view in this file:

- P vs NP becomes a question about **which structural constraints hold**.
- If they hold, Collapse is **forced** — not chosen.
- Decision vs search is explicit: you must also justify extraction, not just
  decidability.
- The frontier `S1Rel_TSP` adds a provability layer that is absent in standard
  complexity treatments.

## Practical interpretation

The file shows that under certain meta-theoretic constraints (DetectsMono,
OmegaAdmissible, completeness, effective extraction), the framework **derives**
Collapse as a consequence. This means TSP admits an efficient search procedure
in this setting — not because we assumed it, but because the dynamics force it.
