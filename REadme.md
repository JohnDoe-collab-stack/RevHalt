# RevHalt

RevHalt is a Lean 4 (Mathlib) formalization of a single idea:

**Turn an impossibility (undecidability of halting) into a navigable structure.**

### The Core Insight: Algebra over Logic

Traditional computability theory treats Halting as a **logical** problem (Truth/Falsity, subject to Logic).
RevHalt treats it as a **geometric** problem (Kernel/Signal, subject to Structure).

By defining `Stabilizes` as the **Kernel** of a monotonous operator (`up T = ⊥`), we transform the "negative verdict" from a logical impossible (proving a negative) into a structural invariant. The "choice" (EM) is merely the coordinate system; the "verdict" is a geometric fact.

---

## The Problem That Couldn't Be Stated

Before RevHalt, we knew:
- **Gödel/Turing**: "There exist true but unprovable statements"
- **AC**: "Selection functions exist" (postulated)
- **EM**: "Every proposition has a truth value" (postulated)

We couldn't clearly distinguish when a "selection" requires AC versus when it requires only EM.

**RevHalt answers**: A dichotomy is **structural** (EM-regime, not AC) when:
1. It comes from a **structural operator** (idempotent, monotone, with universal property)
2. The **kernel** of the operator characterizes one side (theorem, not definition)
3. The **signal** is preserved by the operator
4. The "selection" is a **reading of membership**, not a choice among alternatives

---

## The Abstract Schema

```lean
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  O : X → X                           -- The operator
  mono : Monotone O                   -- Monotonicity
  idem : ∀ x, O (O x) = O x          -- Idempotence
  Sig : X → Prop                      -- The "signal" (Σ₁-like)
  sig_invar : ∀ x, Sig (O x) ↔ Sig x -- Signal preservation
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x   -- Kernel = ¬Signal (Π₁-like)
````

**Where EM enters** (and ONLY here):

```lean
-- Constructive: O x ≠ ⊥ → ¬¬Sig x
theorem ne_bot_imp_notnot_sig : D.O x ≠ ⊥ → ¬¬ D.Sig x

-- Classical (requires EM): O x ≠ ⊥ → Sig x
theorem ne_bot_imp_sig : D.O x ≠ ⊥ → D.Sig x
```

**AC is NOT needed** (nuanced): the oracle/side is external, but once the side is given,
the certificate content is forced by `ker_iff` (structure, not choice).

**Noncomputability policy**: we avoid `noncomputable`. When needed, we use classical reasoning (`by_cases`) only at the “decide the side” point.

---

## Instantiation: Trace/up

RevHalt instantiates the schema with:

```lean
def traceSD : StructuralDichotomy Trace where
  O := up
  mono := up_mono
  idem := up_idem
  Sig := Halts
  sig_invar := exists_up_iff
  ker_iff := up_eq_bot_iff
```

Where:

* `up T n := ∃ k ≤ n, T k` (cumulative monotonization)
* `Halts T := ∃ n, T n` (Σ₁ signal)
* `Stabilizes T := ∀ n, ¬ T n` (Π₁ = kernel of up)

Key fact (proved, not assumed):

```lean
up T = ⊥ ↔ ∀ n, ¬ T n
```

---

## Separation of Principles

| Principle         | Role in RevHalt                                     |
| ----------------- | --------------------------------------------------- |
| **Structure**     | O, ker_iff, sig_invar — theorems about the operator |
| **EM**            | Deciding which side (one point: `¬¬P → P`)          |
| **AC**            | NOT needed — “selection” is forced by structure     |
| **Computability** | Blocked by T2 — uniform decision impossible         |

This separation is the core contribution: **the “choice” in PickOracle is not arbitrary selection (AC), but structural reading (EM + geometry of `up`).**

---

## The Triptych (T1 / T2 / T3)

### T1 — Rigidity

```lean
Rev0_K K T ↔ Halts T
```

Any valid kit collapses to standard halting. `up` supplies the structural operator (kernel identification + signal invariance); kits merely read the induced dichotomy.

### T2 — Uniform Barrier

No internal predicate can be simultaneously total + correct + complete + r.e.

The barrier lives in **uniformity** (`∃H.∀e`), not in **access**.

### T3 — Local Navigation

For each code `e`, a certificate selects the correct side:

* `encode_halt e` (with `Rev0_K` witness) — Σ₁
* `encode_not_halt e` (with `KitStabilizes` witness) — Π₁

**Quantifier Swap**:

* T2 forbids: `∃H ∀e` (uniform)
* T3 permits: `∀e ∃Sₑ` (instancewise)

---

## Abstract Dynamics

The dynamics is **independent of Trace/up**. It depends only on:

```lean
structure PickWorld (Index PropT : Type) where
  Truth : PropT → Prop
  pick : Index → PropT
  pick_true : ∀ i, Truth (pick i)
```

Given this, we get **for free**:

* Soundness preservation (`chain_sound`, `lim_sound`)
* Closed form (`chain_closed_form`, `lim_closed_form`)
* Schedule independence under fairness (`lim_eq_of_fair_schedules`)
* Canonical ω-state (`omegaState`)
* Minimality (`omegaState_minimal`)
* Constructive existence of fair schedule (`exists_fair_limit_eq_omegaState`)

---

## Navigation Dynamics

### The Canonical ω-State

```lean
omegaState.S = S0.S ∪ AllPicks
```

Properties (relative to a pick oracle / PickWorld):

* **Sound**: all members are true
* **Coverage (fairness)**: under a fair schedule, every index’s pick appears in the limit
* **Minimal**: smallest sound extension containing the base and all picks
* **Canonical (confluence)**: independent of fair schedule (same ω-limit)

### ω-Stage Structure

* `Chain n` : state at step `n : ℕ`
* `lim` : the ω-union (limit) of the chain
* `omegaState` : the canonical closure at ω (under fairness + picks)

ω is the correct stage:

* not less (Π₁-style “no witness ever” is a limit phenomenon)
* not more (countable coverage via fair scheduling)

---

## For P vs NP

The testable criterion:

**Does there exist an operator O, natural in a poly-constrained category, such that:**

1. O is functorial w.r.t. poly reductions
2. O has a universal property (adjoint/coreflector)
3. `O φ = ⊥ ↔ UNSAT φ` (non-tautological theorem)
4. `SAT (O φ) ↔ SAT φ` (signal preservation)

**If yes**: NP/coNP is structural like Σ₁/Π₁. P vs NP becomes “is the structure poly-readable?”

**If no**: SAT/UNSAT has no comparable canonical operator geometry in the poly world (a different structural regime).

---

## File Map

### Base Layer

* `RevHalt/Base/Trace.lean` — `Trace`, `Halts`, `up`
* `RevHalt/Base/Kit.lean` — `RHKit`, `DetectsMonotone`, `Rev0_K`

### Theory Layer

* `RevHalt/Theory/Canonicity.lean` — T1 (`T1_traces`, `T1_uniqueness`)
* `RevHalt/Theory/Impossibility.lean` — T2 (`diagonal_bridge`, `T2_impossibility`)
* `RevHalt/Theory/Complementarity.lean` — T3 (`OraclePick`, `S1Set`, `S3Set`)
* `RevHalt/Theory/Stabilization.lean` — `Stabilizes`, `KitStabilizes`, kernel link
* `RevHalt/Theory/Categorical.lean` — `up` as coreflector, `CloE`, `Frontier`
* `RevHalt/Theory/QuantifierSwap.lean` — Quantifier Swap principle
* `RevHalt/Theory/ThreeBlocksArchitecture.lean` — OracleMachine, o-bridge
* `RevHalt/Theory/Dynamics.lean` — Navigation dynamics
* `RevHalt/Theory/WitnessLogic.lean` — Witness soundness

### Abstract Layer (NEW)

* `StructuralDichotomy.lean` — Abstract schema + Trace/up instantiation
* `AbstractDynamics.lean` — Schedule-independent dynamics from PickWorld
* `SD_Bridge.lean` — SDOracle → PickWorld morphism (no classical, no noncomputable)

---

## Core Theorems

| Theorem                 | Statement                                | Significance                   |
| ----------------------- | ---------------------------------------- | ------------------------------ |
| `up_eq_bot_iff`         | `up T = ⊥ ↔ ∀n. ¬T n`                    | Π₁ = kernel (algebraization)   |
| `T1_traces`             | `Rev0_K K T ↔ Halts T`                   | Kit rigidity                   |
| `T2_impossibility`      | No total+correct+complete+r.e. predicate | Uniform barrier                |
| `lim_schedule_free`     | Limit = S₀ ∪ AllPicks                    | Schedule independence          |
| `omegaState_minimal`    | ω-state is smallest extension            | Closure property               |
| `sig_iff_ne_bot`        | `Sig x ↔ O x ≠ ⊥`                        | Abstract dichotomy (classical) |
| `ne_bot_imp_notnot_sig` | `O x ≠ ⊥ → ¬¬Sig x`                      | Constructive content           |
| `dichotomy_all_iff_em`  | `Dichotomy ↔ EM`                         | Ordinal/Class Boundary         |

---

## Build

```bash
lake build
```

---

## What RevHalt Does

Transforms a question about **limits** (undecidability) into a question about **structure** (operators, kernels, closures).

The problem that couldn't be stated:

> "When is a dichotomy structural rather than extensional?"

Answer: when it instantiates `StructuralDichotomy`.

The criterion is now **code**, not prose.

---

## License / Contribution

Add your license and contribution conventions here.

