# RevHalt

RevHalt is a Lean 4 (Mathlib) formalization of a single idea:

**Turn an impossibility (uniform undecidability) into a navigable structure.**

### The Core Insight: Algebra over Logic

Traditional computability theory treats halting primarily as a **logical** question (truth/falsity of “halts”).
RevHalt isolates a **structural** regime in which the negative side is witnessed as a **kernel condition** of an operator.

Concretely, for traces `T : ℕ → Prop` and the cumulative operator

```lean
up T n := ∃ k ≤ n, T k
```

RevHalt proves the key kernel fact (not assumed):

```lean
up T = ⊥ ↔ ∀ n, ¬ T n
```

Thus the Π₁-style “no witness ever” side is captured by an algebraic invariant (`up T = ⊥`), while the Σ₁-style side remains a witness (`∃ n, T n`). The “choice of side” is a semantic/evaluation capability; the certificate shape is forced by structure.

---

## A Machine-Checkable Criterion: Structural vs Extensional Dichotomy

RevHalt’s criterion is: a dichotomy is **structural** when it is induced by an operator with:

1. **Monotonicity + idempotence** (closure-like behavior)
2. A **signal** preserved by the operator
3. A **kernel characterization** identifying the negative side as membership in `ker(O)` (i.e. `O x = ⊥`)
4. Branch selection that is a **reading of membership** (signal vs kernel), not arbitrary choice among alternatives

This is encoded as:

```lean
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  O : X → X
  mono : Monotone O
  idem : ∀ x, O (O x) = O x
  Sig : X → Prop
  sig_invar : ∀ x, Sig (O x) ↔ Sig x
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x
```

---

## Where EM Enters (precisely)

From `ker_iff`, one gets constructively that non-kernel implies double-negated signal:

```lean
theorem ne_bot_imp_notnot_sig : D.O x ≠ ⊥ → ¬¬ D.Sig x
```

To turn this into a positive signal claim requires an evaluation principle such as EM (or any principle giving `¬¬P → P` for the relevant `P`):

```lean
-- classical/evaluative step
theorem ne_bot_imp_sig : D.O x ≠ ⊥ → D.Sig x
```

Interpretation: **structure forces the certificate form** (kernel equality vs signal witness); EM is needed only to **select** the branch by converting `¬¬Sig` into `Sig`.

---

## Instantiation: Trace / up

RevHalt instantiates `StructuralDichotomy` with:

```lean
def Trace := ℕ → Prop

def Halts (T : Trace) : Prop := ∃ n, T n
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

def traceSD : StructuralDichotomy Trace where
  O := up
  mono := up_mono
  idem := up_idem
  Sig := Halts
  sig_invar := exists_up_iff
  ker_iff := up_eq_bot_iff
```

Key proved fact:

```lean
up T = ⊥ ↔ Stabilizes T
```

So the negative verdict is not “just a negation”; it is equivalently a kernel statement in the closure geometry induced by `up`.

---

## Separation of Principles (as used in RevHalt)

| Principle           | Role in RevHalt                                                                                                             |
| ------------------- | --------------------------------------------------------------------------------------------------------------------------- |
| **Structure**       | `O`, `sig_invar`, `ker_iff` — operator theorems fixing certificate form                                                     |
| **EM / evaluation** | branch selection (`¬¬Sig → Sig`) when required                                                                              |
| **AC**              | no internal use is required to *determine certificate content once a side is provided*; the oracle is an external parameter |
| **Computability**   | blocked by T2: no uniform internal total decider                                                                            |

---

## The Triptych (T1 / T2 / T3)

### T1 — Rigidity

```lean
Rev0_K K T ↔ Halts T
```

Any valid kit collapses to the Σ₁ signal (halting-on-traces). The operator supplies the induced dichotomy; kits can only read it.

### T2 — Uniform Barrier

No internal predicate can be simultaneously total + correct + complete + r.e. in the uniform sense.
The obstruction is a **uniformity** barrier (`∃H.∀e`), not the existence of instancewise certificates.

### T3 — Local Navigation

Instancewise, certificates exist (`∀e ∃Sₑ`), yielding a navigable regime without a uniform decider (`∃H ∀e`).

---

## Abstract Dynamics (independent of Trace/up)

```lean
structure PickWorld (Index PropT : Type) where
  Truth : PropT → Prop
  pick : Index → PropT
  pick_true : ∀ i, Truth (pick i)
```

From this, the project derives soundness preservation, closed forms, and ω-limit confluence under fairness.

---

## P vs NP (conceptual criterion only)

This section is a *criterion*, not a formalization: it asks whether there exists a “poly-natural” closure-like operator with kernel/signal properties analogous to the Σ₁/Π₁ regime.

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
| `stage_zero_is_em`      | Stage 0 + Arbitrary = EM                 | Class gap is primary           |
| `decidable_limit_iff_lpo`| Limit + Decidable = LPO                 | Ordinal gap is secondary       |
| `dichotomy_all_iff_em`  | `Dichotomy ↔ EM`                         | Ordinal/Class Boundary         |

---

## Build

```bash
lake build
```

---

## License / Contribution

Add your license and contribution conventions here.
