# Evaluation Mechanism: The Three Referentials

## Overview

RevHalt does not presuppose evaluation as an axiom. Instead, it **parameterizes** evaluation and studies it as an object. This document describes the three referentials (R1/R2/R3) and the precise relationship between EM and LPO.

---

## 0. The Three Referentials

### R1 — Syntax (Formation Referential)

What matters here: which objects exist — which "sentences", which contexts Gamma, which sequences `s : N -> Sentence` are admissible.

**Key point**: Changing the referential changes the available syntax, therefore changes the meaning of "forall s".

### R2 — Semantics (Truth)

A predicate `Truth(p)` that says what is "true" in the intended semantics.

**Key point**: This level is NOT "classical by default". EM here is a **possible property** of the semantics, not an imposed axiom.

### R3 — Evaluation (Operational Access)

A mechanism `Eval(Gamma, phi)` that gives effective (or not) access to verdicts.

**Key point**: "Classical" principles appear here as **access capabilities**.

---

## 1. What "EM" Means at the Evaluation Level (R3)

```
EM_Eval(Gamma) = pointwise capability:

  forall phi, Eval(Gamma, phi) OR NOT Eval(Gamma, phi)
```

**Key point**: This only talks about unitary judgments. It is the "local classical" brick — deciding a single evaluation call.

---

## 2. What "LPO" Means at the Evaluation Level (R3)

```
LPO_Eval(Gamma) = omega/stream capability (ordinal jump):

  forall s : N -> Sentence (admissible in R1),
    (exists n, Eval(Gamma, s(n))) OR (forall n, NOT Eval(Gamma, s(n)))
```

**Key point**: This is **in general stronger** than EM_Eval because it decides an "exists" along an infinite sequence. However, the **strict separation depends on R1**: if R1 restricts the admissible sequences strongly enough, LPO_Eval can collapse and no longer exceed EM_Eval. The implication `LPO_Eval => EM_Eval` itself requires R1 to admit constant sequences.

---

## 3. Correct Order: "EM then LPO" in This Framework

EM comes first as a local capability, then LPO as an omega capability.

### Chronology / Capability Layers

1. Define and examine pointwise evaluation (EM_Eval)
2. Then ask if the evaluation can climb to infinity (LPO_Eval)

### Logical Dependency (Important)

```
LPO_Eval(Gamma) => EM_Eval(Gamma)
```

(constant sequence trick — proved in `RelativeFoundations.lean`)

But the converse is FALSE in general:

```
EM_Eval(Gamma) =/=> LPO_Eval(Gamma)
```

**Conclusion**: LPO "contains" EM, but foundational analysis starts by isolating EM (pointwise), then identifies the ordinal jump LPO.

---

## 4. Where the Referential (R1) Is Decisive

LPO_Eval quantifies over "forall sequences s".

But here, "forall sequences" means "forall sequences formable/admissible in the syntactic referential".

**Therefore**: "being in LPO" is not an absolute label — it is **LPO relative to a grammar of sequences**.

This is exactly where "being on EM" and "being on LPO" differ:

- **EM_Eval** barely depends on the class of sequences (it is pointwise)
- **LPO_Eval** massively depends on what the syntax authorizes as `s`

---

## 5. How This Touches Collatz (Mechanism Only)

For a fixed `n`, Collatz (or "hits 1") is a proposition of the form:

```
exists k, P(n, k)
```

where `P(n, k)` is decidable (compute k steps and test "= 1").

- **EM_Eval** gives you: for each fixed k, you can decide `Eval(Gamma, phi_{n,k})` — but this only works if there is a **bridge** (R1 -> R2/R3) that identifies the sentence `phi_{n,k}` with `P(n, k)` at the relevant level
- But Collatz asks: decide the existence over k, i.e., "exists k" vs "forall k NOT"

At the Evaluation level, this is exactly a case of **LPO_Eval** applied to the sequence `s(k) := phi_{n,k}` (the sentence encoding "test P(n, k)"). The passage `phi_{n,k} <-> P(n, k)` depends on the bridge you have chosen.

**Conclusion**: Understanding the role of LPO in evaluation means understanding the jump "pointwise -> existence over omega" which is precisely the type of step needed for "exists k" statements.

---

## 6. Summary: The Three Key Theorems

| Statement | Truth Value | Justification |
|-----------|-------------|---------------|
| The schema (signal/kernel/up) replicates at the evaluative level | TRUE | Same form: `upE` in `RelativeFoundations.lean` |
| The evaluative dichotomy IS LPO_Eval | TRUE | Proved by `DichotomyE_iff_LPO_Eval` |
| The Base case (Truth=id) collapses to global EM | TRUE | Because R1 authorizes injection `P -> constTrace P`, which brings back EM at stage 0 (`stage_zero_is_em`) |

---

## 7. File Pointers

| Concept | File |
|---------|------|
| Base definitions (Trace, Halts, up) | `RevHalt/Base/Trace.lean` |
| Kit and DetectsMonotone | `RevHalt/Base/Kit.lean` |
| T1 (Canonicity) | `RevHalt/Theory/Canonicity.lean` |
| T2 (Impossibility) | `RevHalt/Theory/Impossibility.lean` |
| T3 (Complementarity, OraclePick) | `RevHalt/Theory/Complementarity.lean` |
| Stabilization as kernel | `RevHalt/Theory/Stabilization.lean` |
| EM_Truth, LPO_Truth, EM_Eval, LPO_Eval, upE | `RevHalt/Theory/RelativeFoundations.lean` |
| stage_zero_is_em, dichotomy_iff_em | `RevHalt/Theory/OrdinalMechanical.lean` |
| Ordinal boundary (constructive vs classical) | `RevHalt/Theory/OrdinalBoundary.lean` |
| StructuralDichotomy schema | `RevHalt/Theory/StructuralDichotomy.lean` |
| AbstractDynamics (PickWorld) | `RevHalt/Theory/AbstractDynamics.lean` |
| Dynamics (Chain, lim, omegaState) | `RevHalt/Theory/Dynamics.lean` |
| SD_Bridge (SDOracle -> PickWorld) | `RevHalt/Theory/SD_Bridge.lean` |
| Quantifier Swap (T2 vs T3) | `RevHalt/Theory/QuantifierSwap.lean` |
| CollatzBoundary (LPO isolation) | `RevHalt/Theory/CollatzBoundary.lean` |

---

## 8. The Fundamental Insight

RevHalt does not say "we can solve the halting problem".

RevHalt says:

1. **The geometry (kernel vs signal) is structural** — provable without evaluation
2. **Evaluation (deciding the side) is exactly EM/LPO** — characterized as equivalence
3. **The degenerate case (Prop, id) shows that quantifying over arbitrary propositions == EM**

The evaluation mechanism is **not a hypothesis** of the project — it is its **object of study**. The project **localizes** where and in what form evaluation is necessary.
