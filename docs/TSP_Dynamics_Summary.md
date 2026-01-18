# TSP dynamics: chain to Collapse (no latex)

This note summarizes what the TSP instance proves in the dynamic framework.

---

## 1) Goal

Produce a precise output object:

```
Collapse_TSP_Axiom
```

not by postulating it, but by a trajectory-dependent chain.

---

## 2) Inputs (explicit parameters)

The API takes concrete parameters, not hidden assumptions:

- Trajectory choices:
  - Absorbable at step 1
  - OmegaAdmissible at omega
- Chain invariants:
  - CnExtensive, CnIdem, ProvClosedCn, ProvRelMonotone
- Cost token:
  - PolyCompressionWC_TSP at omega

These are exposed as arguments in:

```
Collapse_TSP_of_TrajectoryChoice_and_PriceOfP
```

---

## 3) Core chain (what is derived)

The formal chain is:

```
Absorbable and OmegaAdmissible -> not RouteIIAt
not RouteIIAt -> S1Rel = empty
S1Rel = empty + PriceOfP -> Collapse_TSP_Axiom
```

Each step is a named lemma, and the composition is explicit.

---

## 4) What this means

- The result is trajectory-dependent.
- Collapse is an output of the framework, not a hidden axiom.
- The cost parameter (Price of P) is localized and consumed exactly where needed.

---

## 5) Where it lives

- `RevHalt/Theory/Instances/TSP_Dynamics.lean`
- `RevHalt/Theory/Instances/TSP_Canonization.lean`
- `RevHalt/Theory/Instances/TSP.lean`

---

## 6) One-line summary

The TSP instance is resolved inside the dynamic framework:

```
Trajectory choices + structural invariants + PriceOfP
-> stability -> canonization -> Collapse_TSP_Axiom
```

---

## 7) Fixed point (policy lens: ZFC / Lawvere / Tarski)

This TSP chain does not require fixed points.
However, the library makes the fixed-point forcing mechanism explicit.

### 7.1 Fixed point is a theorem under a policy + continuity

There are two formal fixed-point schemata in the code:
Here F is the theory transformer (e.g. F0 in TheoryDynamics), and
omegaUnion (iter F Γ0) is the omega-limit of the iterative chain under
the chosen LimitOp.

(A) omega-chain (natural iteration):
  - OmegaContinuousSet F -> F(omegaUnion (iter F Γ0)) = omegaUnion (iter F Γ0)
    (theorem: omega_fixpoint_of_OmegaContinuousSet in TheoryDynamics.lean)
  - no fixpoint -> not OmegaContinuousSet
    (theorem: not_omegaContinuous_of_no_fixpoint)

(B) transfinite iteration (ordinal limit):
  - ContinuousAt F A0 lim + extensivity -> F(Γ_lim) = Γ_lim
    (theorem: continuous_implies_fixpoint_at_limit in TheoryDynamics_Transfinite.lean)

### 7.2 Limit policy is an explicit design choice

Limit policy is parameterized by LimitOp:
  - unionLimitOp      : limit = union
  - cnUnionLimitOp Cn : limit = Cn(union)
  - jumpLimitOp Cn J  : limit = union + jump, then closed

So a fixed point at omega is not "natural"; it is produced by:
  chosen LimitOp + continuity for that iteration.

### 7.3 Conceptual mapping (non-essential lens)

This project does not use the Lawvere/Tarski method; it treats fixed points
as artifacts of explicit policy + continuity, not as a diagonalization route.

- ZFC lens:
  common practice treats omega limits as unions of stages.
  In this library that practice is unionLimitOp / cnUnionLimitOp,
  and it is exposed as a policy, not a default.

- Lawvere lens:
  diagonal or self-reference is a source of fixed points when the ambient
  structure provides the right evaluation and continuity channel.

- Tarski lens:
  full internal closure of truth is not free; enforcing closure at the same
  level requires stratification or a policy choice. Here, the policy is
  explicit (LimitOp), and the dynamic layer shows where stabilization is forced.

### 7.4 Separation: frontier empty vs fixed point

Frontier empty (S1Rel = empty) and fixed point (F(Γ_omega) = Γ_omega) are
distinct notions in the library. There are explicit bridges between them
(for example fixpoint_implies_OmegaAdmissible), but they are not identical.
