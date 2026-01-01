# RevHalt: The Kinetic Continuation Architecture

## Status

This document synthesizes the rigorous structural contribution of RevHalt. The central point (technical, not rhetorical) is this:

**Turing-type undecidability (T2) does not say "truth is inaccessible". It says: "there is no uniform, static, closed decider internal to a fixed framework that settles all instances."**

RevHalt formalizes this shift by cleanly separating three notions often confused.

---

## 1. Decidability, Evaluation, EM (and where LPO sits)

### (a) Decidability (Constructive)
It is a property of a given statement P: we know how to decide P (in the effective/constructive sense), i.e., obtain P OR NOT P for that specific P. We can have "pointwise" decidability on a family P(n) without having a global principle.

### (b) Evaluation (R3)
It is a parameterized mechanism (Eval(Gamma, phi)) representing operational access: a procedure, an oracle, a local reading, a verification device, etc.
**Important**: Eval is not a logical axiom. It is a given (or a parameter) whose capabilities we study. In particular, Eval can be restricted by formation (R1) and is not intended to "see" all possible sentences.

### (c) EM (Excluded Middle)
It is a logical principle.
*   **Global EM**: For all P:Prop, P OR NOT P.
*   **EM_Eval (local to evaluator)**: For all phi, Eval(Gamma, phi) OR NOT Eval(Gamma, phi). This is a property of the access (R3), not automatically a global logic property.

### (d) LPO (omega-jump) at Evaluation Level
LPO_Eval is stronger than EM_Eval: it settles an "EXISTS along omega" for sequences of sentences. In the reference frame, this is not "absolute LPO", it is **LPO relative to a grammar R1**: we do not quantify over all sequences s, only over those authorized by R1.

---

## 2. What T2 Forbids Exactly (and Only)

T2 forbids a **single static object** (an H) which, within the **same fixed framework** (same formable objects, same class of admissible sequences, same internal access), would uniformly decide all instances.

In other words: T2 targets **Uniformity + Closure** (a single internal mechanism, valid for everything, without extending the frame).

---

## 3. What RevHalt Puts in Place (T3): Kinetic Continuation

Instead of seeking a global H, RevHalt formalizes an **extension dynamic**:

> For each instance e, we can construct a **local extension** S_e (or a chain step) that adds the relevant information for e, in a controlled way.

**The Technical Point**: "Decision" is no longer a global verdict posited at the start. It is a **trajectory of refinements** (a kinetics) whose limit horizon corresponds to the "global" -- but this "global" is not a static starting hypothesis.

This does not contradict T2: it reformulates what T2 blocks (the uniform and closed decider) and what remains possible (verifiable local extensions).

---

## 4. The Second Operational Pivot: Rigidifying the Negative (Pi-1) as Structure

In standard theory, "non-halting / stabilization" is often treated as a "ghost" negation: NOT Halts(T), hence a Pi-1 condition difficult to manipulate constructively.

RevHalt replaces it with a **structural characterization**: stabilization becomes an **algebraic property** (membership in a kernel) via a closure operator (like `up`).

The "NO" is no longer just "absence of proof of halting", it is "presence of a structural nullity" (kernel).
**Consequence**: We can work with Pi-1 as a manipulable object, independent of the ability to settle the omega-jump by an evaluator.

---

## 5. Why the R1/R3 Separation Avoids "LPO implies EM" Slips

Many collapses towards EM rely on an implicit schema: "we quantify over ALL sequences, INCLUDING CONSTANTS". If R1 restricts admissible sequences (and particularly if constants are not admissible), then the passage "LPO (on grammar) implies EM_Eval (on everything)" is no longer automatic: the collapse mechanism is localized and controllable.

So the correct analysis is not "LPO is dangerous because it implies EM", but:
1.  **Which LPO** (relative to which grammar R1)?
2.  **Which EM** (global, or only EM_Eval on a sub-universe of sentences)?
3.  **Which Access** (Eval) is actually assumed?

---

## Summary
RevHalt does not "make the undecidable decidable". It:
1.  **Isolates** T2 undecidability as a constraint of uniformity/closure.
2.  **Replaces** the impossible demand for a global decider with a **kinetics of local extensions** (T3).
3.  **Rigidifies** the negative (stabilization) into a **structural object** (kernel), while cleanly distinguishing decidability, evaluation, EM, and the omega-jump (LPO) relativized to R1.
