# Conceptual solution for TSP in RevHalt

This note explains the conceptual "solution" path in `TSP.lean` and how it
differs from the usual treatment of TSP and P vs NP.

## What "solution" means here

The file does not give a new algorithm for TSP. It gives a formal bridge from:

- a concrete NP problem (TSP),
- to halting and provability dynamics (RevHalt),
- and to a **conditional** statement about search/decision procedures.

So the "solution" is a meta-theoretic pipeline: encode, model, relate halting,
then show how certain **hypothesis packages and trajectory choices** yield a
Collapse-style search procedure.

## Core conceptual steps

1) Computable encodings

- Tours, graphs, and instances are encoded into natural numbers.
- Decoding is constructive, with roundtrip lemmas to show no information is lost.

1) Machine semantics

- A trace enumerates tours and checks validity.
- The key equivalence is: the machine halts iff a valid tour exists.

1) Frontier and trajectory

- `S1Rel_TSP` captures true-but-unprovable halting statements in a theory state.
- Note: `S1Rel_TSP` uses `Halts`, while generic `S1Rel` uses `Rev0_K`.
  A bridge lemma (via `DetectsMono`) is needed to relate them.
- Trajectory operators iterate theory enrichment and define an omega limit.

1) Route II and the trilemma

- Route II is a **separate hypothesis package** (soundness, negative completeness,
  barrier) about an external semantic layer — not given by TSP structure alone.
- The trilemma proves: ¬(Absorbable ∧ OmegaAdmissible ∧ RouteIIAt).
- To conclude ¬RouteIIAt, you must **commit** to keeping Absorbable and
  OmegaAdmissible. This is a **trajectory choice**, not a forced implication.

1) Canonization and Collapse

- **Given** ¬RouteIIAt (from trajectory choice), you get PosComplete at ω.
- **Given** NegComplete (additional hypothesis), you get full Canonization.
- **Given** effective extraction data, you can construct a Collapse procedure.
- Collapse is therefore derived from effective canonization **data**, not forced
  by dynamics alone.

## What is assumed vs what is derived

| **Assumed / Given** | **Derived** |
|---------------------|-------------|
| Route II hypothesis package | Trilemma disjunction |
| Trajectory choice: keep Absorbable + OmegaAdmissible | ¬RouteIIAt |
| DetectsMono K (for Halts↔Rev0_K bridge) | S1Rel_TSP alignment |
| NegComplete | Full Canonization |
| EffectiveCanonizationAtOmega (data) | **Collapse** (theorem) |

**Important**: The existence of `EffectiveCanonizationAtOmega` is itself an
assumption/data source unless you prove the trajectory produces it. Collapse is
"derived from effective canonization data," not "forced by dynamics" in a strong
unconditional sense.

## What changes vs the usual view

Usual view:

- TSP is NP-complete; P vs NP is a single global question.
- Proofs focus on reductions and algorithmic lower/upper bounds.

RevHalt view in this file:

- P vs NP becomes a question about **which hypothesis packages hold** and
  **which trajectory choices you make**.
- If they hold and you make those choices, Collapse follows.
- Decision vs search is explicit: you must also justify extraction, not just
  decidability.
- The frontier `S1Rel_TSP` adds a provability layer that is absent in standard
  complexity treatments.

## Complexity caveat

`Collapse_TSP_Axiom` says "exists Find" but does not formalize or prove
a polynomial bound. "Efficient" remains informal unless resource bounds are
modeled explicitly.

## Summary (accurate version)

The file shows a **conditional pipeline**:

**Given** the Route II hypothesis package and **given** a trajectory choice that
preserves Absorbable + OmegaAdmissible, you obtain ¬RouteIIAt.

From that (plus the Halts↔Rev0_K bridge if using generic S1Rel) you get
PosComplete-at-ω.

Adding NegComplete and effective canonization data yields a Collapse-style
search/decision procedure.
