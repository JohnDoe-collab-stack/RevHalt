# Fixpoint in RevHalt (exhaustive, no latex)

This note lists the fixpoint-related definitions and lemmas as they appear in the transfinite and jump modules.

---

## 1) Core objects (transfinite dynamics)

Definitions in `RevHalt/Theory/TheoryDynamics_Transfinite.lean`:

- `transUnion (chain, lim)`
  - transfinite union of a global chain up to a limit

- `transUnionFamily (chain)`
  - union of a dependent family (used in limit recursion)

- `LimitOp`
  - limit operator with `apply : (forall beta < alpha, Set PropT) -> Set PropT`

- `LimitDecomp`
  - decomposition of a limit operator through a global chain

- `unionLimitOp`
  - limit = transUnionFamily

- `cnUnionLimitOp Cn`
  - limit = Cn(transUnionFamily)

- `transIterL L F A0 alpha`
  - transfinite iteration using limit operator L

- `transIter F A0 alpha`
  - abbreviation for `transIterL unionLimitOp F A0 alpha`

Basic recursion lemmas:

- `transIterL_zero`
- `transIterL_succ`
- `transIterL_limit`
- `transIter_zero`
- `transIter_succ`
- `transIter_limit`

Limit-stage inclusion:

- `LimitIncludesStages L F A0`
- `limitIncludesStages_of_decomp`
- `limitIncludesStages_union`

Monotonicity:

- `transIter_mono`

---

## 2) Continuity and fixpoint (transfinite)

Definitions in `RevHalt/Theory/TheoryDynamics_Transfinite.lean`:

- `ContinuousAt F A0 lim`
  - continuity at a limit for union-style iteration

- `ContinuousAtL L F A0 lim`
  - continuity at a limit for a general `LimitOp`

- `FixpointFromContinuity L F A0 lim`
  - explicit contract: `ContinuousAtL ... -> F (transIterL L F A0 lim) = transIterL L F A0 lim`

Fixpoint lemma at a limit (union style):

- `continuous_implies_fixpoint_at_limit`
  - requires `hExt : forall Γ, Γ ⊆ F Γ`
  - conclusion: `F (transIter F A0 lim) = transIter F A0 lim`

Bridge to admissibility:

- `fixpoint_implies_OmegaAdmissible`

---

## 3) Frontier collapse schema at limits

Definitions/lemmas in `RevHalt/Theory/TheoryDynamics_Transfinite.lean`:

- `FrontierInjected F`
- `frontierInjected_of_CnExt`

Collapse at limits:

- `limit_collapse_schema_L`
- `limit_collapse_schema_Decomp`
- `limit_collapse_schema`

---

## 4) Structural escape (limit-level no-continuity)

Key lemmas in `RevHalt/Theory/TheoryDynamics_Transfinite.lean`:

- `structural_escape_transfinite`
- `structural_escape_at_limit`

Parametric L-version (requires explicit fixpoint contract):

- `structural_escape_transfinite_L`
- `structural_escape_at_limit_L`

Fork law (no continuity if fixpoint contract holds):

- `fork_law_False`
- `fork_law_not_ContinuousAtL`

Policy-specific endpoint (cnUnion):

- `global_change_of_sense`
- `part7_change_of_sense_cnUnion`

---

## 5) Jump-limit fixpoint (jump continuity)

Lemmas in `RevHalt/Theory/TheoryDynamics_Transfinite_JumpFixpoint.lean`:

- `jump_continuousAtL_implies_fixpoint`
  - continuity at jump limit implies fixpoint at the jump limit

- `jump_fixpoint_from_continuity`
  - packaged form: provides `FixpointFromContinuity` for jump limit operators
  - requires `hExt : forall Γ, Γ ⊆ F Γ`

Jump endpoint (no-continuity under escape hypotheses):

- `part7_change_of_sense_jump`

Jump limit stage inclusion is provided by:

- `limitIncludesStages_jumpLimitOp` in `RevHalt/Theory/TheoryDynamics_Transfinite_Jump.lean`

---

## 6) Definition of fixpoint used by the system

The fixpoint is always evaluated on the limit candidate built by the iteration:

- `Gamma_lim := transIterL L F A0 lim`
- fixpoint statement: `F Gamma_lim = Gamma_lim`

There is no global existential fixpoint axiom; fixpoint is tied to the chosen
limit policy and iteration operator.
