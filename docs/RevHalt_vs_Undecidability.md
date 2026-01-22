# RevHalt vs Classical Undecidability (Structural Contrast)

This note separates two kinds of negative results:

- **Classical undecidability**: impossibility of a uniform total decision procedure.
- **RevHalt dynamics**: structural obstruction to reaching a stable theory state by canonical limit-iteration.

No probability, no real analysis: the framework lives in set-theoretic theory evolution (`Set PropT`) indexed by ordinals, with explicit limit operators.

---

## Classical Undecidability

### Core statement

Undecidability forbids **one single total algorithm** deciding a property for **all** inputs (e.g., Halting).

### Method

Diagonalization constructs an input contradicting any purported decider.

### What it does not analyze

Undecidability does not describe:

- how partial procedures behave,
- how proof search evolves,
- why a specific constructive iteration fails.

It is a **class closure** theorem: "no member of this class can do the job".

---

## RevHalt Contribution

### Core statement (fixpoint-centric)

RevHalt isolates a gap between:

- **existence** of a fixed point (Tarski-style, non-constructive existence in a complete lattice), and
- **accessibility** of a fixed point by canonical limit iteration (Kleene-style, requiring continuity at limits).

In RevHalt, the canonical limit candidate (omega-limit, and more generally limit-stage unions) can be forced **not** to behave like a fixed point under natural structural constraints.

### Mechanism: frontier dynamics and limit collapse

RevHalt defines a frontier operator:

- `S1Rel(Γ)` = "externally certified statements not provable from Γ".

Then the step operator injects frontier content into the next stage:

- `F0(Γ) = Γ ∪ S1Rel(Γ)`,
- `F(Γ) = Cn(F0(Γ))`.

Key structural fact:

- `S1Rel` is **anti-monotone**: if `Γ ⊆ Δ` then `S1Rel(Δ) ⊆ S1Rel(Γ)`.

This anti-monotonicity is the lever behind collapse:

- if an item is missing at a limit stage, it was already missing earlier,
- hence it was eligible for injection early,
- and once absorption holds at some successor stage, injected items become provable,
- therefore frontier survival at limits becomes impossible.

---

## Main RevHalt Theorems

### 1. Limit Collapse Schema

Location: `RevHalt/Theory/TheoryDynamics_Transfinite.lean`, line 398.

If absorption holds at some successor stage before a limit ordinal lambda, then the frontier at lambda collapses to empty.

This repeats at every limit ordinal where a prior absorption event occurs (transfinite schema).

### 2. The omega-Trilemma (obstruction, not classification)

Three natural desiderata cannot hold simultaneously at the omega-limit:

- absorption at an early successor stage,
- admissibility/closure consistency at the limit,
- a nonempty frontier at the limit (RouteII).

Formally: **not all three together**. At least one must fail.

> [!IMPORTANT]
> The trilemma is an obstruction statement, not a classification. It does not claim "exactly one of three regimes applies", but rather "the three desiderata cannot be simultaneously satisfied".

### 3. Structural Escape

If you insist on both:

- absorption (early successor),
- and RouteII at the limit (frontier must remain nonempty),

then the step operator cannot satisfy the continuity condition that would make Kleene's construction work.

Location: `structural_escape_transfinite` in `TheoryDynamics_Transfinite.lean`, line 600.

---

## Comparative Summary

| Aspect | Classical Undecidability | RevHalt Dynamics |
|--------|--------------------------|------------------|
| Core claim | No uniform total decider exists | Canonical limit-iteration cannot satisfy stability constraints |
| Proof style | Diagonalization | Ordinal/limit-stage dynamics with frontier injection |
| What is blocked | A class of algorithms | A procedure schema: limit iteration under continuity/admissibility with active frontier |
| Granularity | Binary: decider exists or not | Structural obstruction: at least one of several natural constraints must fail |
| Nature | Static impossibility | Dynamic mechanism diagnosis |

---

## What RevHalt Adds

RevHalt does not replace undecidability. It explains how and where a natural construction breaks:

- the frontier mechanism forces either
  - loss of continuity at limits,
  - frontier extinction (closed system),
  - or failure of admissibility/closure at limits.

This is a structural, mechanistic statement about theory evolution, independent of probabilistic or real-valued encodings.

---

## Limit-Operator Design Note (Jump is not magic)

**Jump is a design lever, not a silver bullet.** `jumpLimitOp Cn J` changes what happens *at limits* by adding explicit completion content (`U ↦ Cn (U ∪ J U)`), and it supports standard sanity properties (e.g. stage inclusion under `CnExtensive`) plus Kleene-like lemmas of the form “`ContinuousAtL` ⇒ fixpoint”. However, the main obstruction is formulated for an arbitrary `L : LimitOp`: if one keeps the same bundle (absorption below the limit + RouteII at the limit + coherence/fixpoint accessibility requirements), a contradiction can still be forced. So changing the limit operator can help certify alternative architectures, but some bundles remain incompatible unless one weakens absorption/RouteII, enriches the state (two-sided / proof-carrying), or revises what “frontier” means at limits.

---

## Fixpoint Characterization

Under absorption, the operational fixpoint condition reduces to frontier nullity:

- Under `Absorbable Γ`, we have `F0 Γ = Γ` if and only if `S1Rel Γ = ∅`.

This makes the Bulk/Frontier separation non-philosophical: a theory is a fixpoint of the step operator exactly when its frontier is empty.

---

## Formal References

| Theorem | File | Line |
|---------|------|------|
| `limit_collapse_schema` | `TheoryDynamics_Transfinite.lean` | 398 |
| `structural_escape_transfinite` | `TheoryDynamics_Transfinite.lean` | 600 |
| `fork_law_False` | `TheoryDynamics_Transfinite.lean` | 747 |
| `S1Rel_anti_monotone` | `TheoryDynamics.lean` | (core file) |
| `not_JumpDiscontinuousAlong_frontier` | `TheoryDynamics_Transfinite_Jump.lean` | 198 |
