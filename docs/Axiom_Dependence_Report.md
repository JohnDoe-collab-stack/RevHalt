# Axiom dependence (constructive vs classical)

This note classifies key RevHalt theorems by whether they depend on classical axioms,
using Lean’s `#print axioms` output.

Regenerate mechanically by building:

```
lake build RevHalt.Diagnostics.AxiomsReport
```

The report source is:

`RevHalt/Diagnostics/AxiomsReport.lean`

---

## Classification rule used here

- **Constructive (in the “no classical choice” sense)**: the axiom list does **not** contain
  `Classical.choice`.
- **Classical**: the axiom list **does** contain `Classical.choice`.

(`propext` and `Quot.sound` may still appear; they are tracked but not counted as “classical” here.)

---

## Key theorems (from `RevHalt/Diagnostics/AxiomsReport.lean`)

- `RevHalt.omega_trilemma_not_all`
  - axioms: `propext`, `Quot.sound`
  - classification: constructive (no `Classical.choice`)
  - meaning: the “not-all” trilemma form is provable without classical choice.

- `RevHalt.omega_trilemma_disjunction`
  - axioms: `propext`, `Classical.choice`, `Quot.sound`
  - classification: classical
  - meaning: turning the trilemma into an explicit disjunction uses classical choice.

- `RevHalt.F0_pm_monotone_of_provClosed`
  - axioms: none
  - classification: constructive
  - meaning: two-sided monotonicity is constructive given an explicit `DecidablePred` for provability.

- `RevHalt.F0_pm_monotone_classical`
  - axioms: `propext`, `Classical.choice`, `Quot.sound`
  - classification: classical
  - meaning: removing the decidability hypothesis forces a classical step (`Classical.decPred`).

- `RevHalt.continuous_implies_fixpoint_at_limit`
  - axioms: `propext`, `Classical.choice`, `Quot.sound`
  - classification: classical
  - meaning: the transfinite “continuity implies fixpoint” lemma is classical (in this development).

- `RevHalt.TSP.S1Rel_empty_at_omega_of_absorbable_and_admissible`
  - axioms: `propext`, `Classical.choice`, `Quot.sound`
  - classification: classical
  - meaning: even if the *local* proof is written without `classical/by_contra`, the imported route-II/trilemma layer brings in `Classical.choice`.

- `RevHalt.TSP.Collapse_TSP_of_TrajectoryChoice_and_PriceOfP`
  - axioms: `propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Quot.sound`
  - classification: classical (and also depends on Lean’s boolean-reduction/trust-compiler axioms)

---

## Refactors done (removing avoidable `classical/by_contra`)

- `RevHalt/Theory/Instances/TSP_Dynamics.lean`
  - rewrote the final step `¬RouteIIAt -> S1Rel = ∅` to avoid `by_contra` and `Set.nonempty_iff_ne_empty`.

- `RevHalt/Theory/Instances/TSP.lean`
  - rewrote `S1Rel_empty_of_not_RouteIIAt` constructively (same pattern: membership gives `Nonempty`).

- `RevHalt/Theory/TheoryDynamics_Transfinite.lean`
  - removed unnecessary `classical` from `limit_collapse_schema_L`
  - removed `classical` from `limitDecomp_union` (ordinal `<` is decidable here, so the proof does not need global classical).

