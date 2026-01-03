# RevHalt: Operational Foundations and Derived Lenses

RevHalt is a machine-checked (Lean 4 / mathlib) framework for **operational foundations**:
it makes “non-constructive strength” (EM, choice, oracle power, bridges between semantics and execution, …)
an explicit *access interface* rather than an ambient background axiom.

The guiding pattern is:

1. **RevHalt fixes what counts as information and access.**
2. **Derived lenses (ordinal, Scott/topological, diagonal) compute what is observable/decidable/impossible.**
3. **Lean audits where classical power enters, theorem-by-theorem.**

## 1) The RevHalt interface (what you choose)

RevHalt’s core commitments are not “Scott” or “ordinal ω” by default. They are concrete interface choices:

- **Information object**: traces `Trace := ℕ → Prop`.
- **Information order**: pointwise entailment `T ≤ U := ∀ n, T n → U n`.
- **Basepoint**: the empty trace `⊥`.
- **Normalization/projector**: `up : Trace → Trace` (cumulative closure).
- **Three layers (R1/R2/R3)**:
  - R1: what is formable/testable.
  - R2: semantic truth in a model.
  - R3: operational accessibility via evaluation/oracles.
- **Bridges as explicit hypotheses**: e.g. relating `Eval` to semantic consequence (`SemConsequences`) in the 3-block architecture.

Once these are fixed, you can *compute* what is possible without pretending the power is “free”.

## 1.5) Interface → invariants (the “RevHalt machine”)

One way to read the project is as a compiler from **access interfaces** to **foundation-level invariants**.

```
RevHalt interface (you choose)                 Derived lenses (RevHalt computes)
──────────────────────────────────             ───────────────────────────────────────────
Trace := ℕ → Prop                              Scott lens (finite observation)
Order: pointwise entailment  (≤)               - Scott-open/closed regions
Basepoint: ⊥                                   - no nontrivial discrete separation
Normalizer: up                                 (`RevHalt/Theory/ScottTopology.lean`)
R1/R2/R3 + explicit bridges/oracles       ──▶
                                                Ordinal lens (finite → ω / EM boundary)
                                                - dichotomy strength = EM exactly
                                                (`RevHalt/Theory/OrdinalBoundary.lean`)

                                                Diagonal/Gödel lens (internalization barrier)
                                                - no total+correct+complete internalization
                                                - “Gödel-I shape” corollaries (with/without witness)
                                                (`RevHalt/Theory/Impossibility.lean`,
                                                 `RevHalt/Theory/GodelLens.lean`)

                                     Axiom audit channel: `#print axioms ...`
```

The point is not that Scott/ordinals/diagonalization are “new”, but that RevHalt treats them as **outputs**:
change the access interface, and the same lenses re-compute what becomes observable/decidable/impossible.

## 2) Derived lenses (what you get “for free” once the interface is fixed)

### (A) Ordinal boundary (finite → ω)

RevHalt isolates the exact point where you move from finite-stage evidence to ω-completion.
In particular, the global dichotomy is *exactly* excluded middle in strength:

- `RevHalt.OrdinalBoundary.dichotomy_all_iff_em` (`RevHalt/Theory/OrdinalBoundary.lean`)

This is not a slogan: it is a precise equivalence proved inside the development.

### (B) Scott / domain-theoretic lens (finite observability as regions)

Scott/domain language is a **derived vocabulary** for RevHalt’s access interface:
it turns “booleans” into **regions** determined by finite observation / approximation.

RevHalt makes this explicit without relying on mathlib’s `Topology.WithScott` wrappers (which currently introduce `Classical.choice` via equivalences).
Instead it works directly with order-theoretic Scott predicates:

- `IsScottOpen s := IsUpperSet s ∧ DirSupInacc s`
- `IsScottClosed s := IsLowerSet s ∧ DirSupClosed s`

Key consequences:

- `RevHalt.haltsSet_isScottOpen` (Σ₁ / finitely observable)
- `RevHalt.stabilizesSet_isScottClosed` (Π₁ / limit property)
- **Discrete separation obstruction**: any Scott-compatible `f : α → Bool` must be constant
  (`RevHalt.scottCompatibleToBool_const`)

All in `RevHalt/Theory/ScottTopology.lean`.

### (C) Diagonal barrier (Gödel/Lawvere/Kleene pattern)

RevHalt packages the “no total correct complete internalization” pattern as a uniform impossibility theorem:

- `RevHalt.T2_impossibility` (`RevHalt/Theory/Impossibility.lean`)

This is the same skeleton that underlies Gödel-style diagonal arguments, but here it is expressed through the RevHalt interface:
what matters is the ability to internalize a `Rev0_K`-like predicate with the wrong closure properties.

For a “Gödel-I shaped” presentation (still without arithmetizing `PropT`), see the derived lens:

- `RevHalt.not_total_of_correct_complete_semidec`
- `RevHalt.exists_undecidable_classical_of_correct_complete_semidec`
- `RevHalt.exists_true_unprovable_classical_of_correct_complete_semidec`
  (`RevHalt/Theory/GodelLens.lean`)

## 3) Claim map (one-sentence claims → Lean theorems)

This is the “assume RevHalt” checklist: every conceptual sentence should point to a theorem.

- **Stabilization is a kernel, not an opaque negation** → `RevHalt.Stabilizes_iff_up_eq_bot` (`RevHalt/Theory/Stabilization.lean`)
- **Global dichotomy is exactly EM** → `RevHalt.OrdinalBoundary.dichotomy_all_iff_em` (`RevHalt/Theory/OrdinalBoundary.lean`)
- **Halting is Scott-open; stabilization is Scott-closed (order-theoretically, choice-free)** → `RevHalt.haltsSet_isScottOpen`, `RevHalt.stabilizesSet_isScottClosed` (`RevHalt/Theory/ScottTopology.lean`)
- **No Scott-compatible total boolean decider can recognize `Stabilizes`** → `RevHalt.no_scottOpen_bool_decider_for_stabilizes` (`RevHalt/Theory/ScottTopology.lean`)
- **Scott-compatible `Bool` observables are constant (no nontrivial discrete separation)** → `RevHalt.scottCompatibleToBool_const` (`RevHalt/Theory/ScottTopology.lean`)
- **Uniform barrier / diagonal impossibility** → `RevHalt.T2_impossibility` (`RevHalt/Theory/Impossibility.lean`)
- **Gödel lens (non-totality; classical undecidable code)** → `RevHalt.not_total_of_correct_complete_semidec`, `RevHalt.exists_undecidable_classical_of_correct_complete_semidec` (`RevHalt/Theory/GodelLens.lean`)
- **Gödel-I shape (external truth ⇒ true-but-unprovable)** → `RevHalt.exists_true_unprovable_classical_of_correct_complete_semidec` (`RevHalt/Theory/GodelLens.lean`)
- **R1-restricted LPO collapses to EM only if constants are admissible** → `RevHalt.RelativeR1.LPO_R1_imp_EM_if_const` (`RevHalt/Theory/RelativeR1.lean`)

## 4) Axiom hygiene (why the audits matter)

Many files end with `#print axioms ...` to localize exactly where classical principles enter.
For example, `RevHalt/Theory/ScottTopology.lean` is written to avoid `Classical.choice` by avoiding `IsOpen`/`IsClosed` for `WithScott`.

You should treat these audits as part of the theory: they are the mechanism by which “power” is tracked as an explicit capability.

## 5) Non-claims (to keep the story honest)

RevHalt does not claim to “invent Scott topology” or “replace domain theory”.
The novelty is operational:

- it turns foundational strength into **interface design** (access/bridges),
- it makes derived readings (Scott/ordinal/diagonal) **portable across interfaces**,
- and it keeps the story honest via machine-checked **axiom locality**.
