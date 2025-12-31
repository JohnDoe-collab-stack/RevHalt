# RevHalt

A Lean 4 formalization establishing that classical logic (EM) functions as a semantic evaluator rather than a foundational axiom system.

## Main Result

**Theorem.** The total dichotomy for traces is logically equivalent to the Law of Excluded Middle:

```lean
theorem dichotomy_all_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬P)
```

Verified with **zero axioms** beyond Lean's kernel.

**Corollary.** The structure of the dichotomy exists independently of EM. Classical logic provides the capacity to evaluate which side of the partition an element occupies, but does not generate the partition itself.

---

## Formal Content

### 1. Primitive Layer (Zero Axioms)

**Definitions.**

```lean
def Trace := ℕ → Prop
def Halts (T : Trace) : Prop := ∃ n, T n                    -- Σ₁
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n            -- Π₁
def up (T : Trace) : Trace := fun n => ∃ k, k ≤ n ∧ T k    -- Cumulative closure
```

**Structural Theorems.**

| Theorem | Statement | Axioms |
|---------|-----------|--------|
| `up_mono` | `T ≤ U → up T ≤ up U` | 0 |
| `up_idem` | `up (up T) = up T` | 0 |
| `exists_up_iff` | `(∃n, up T n) ↔ (∃n, T n)` | 0 |
| `up_eq_bot_iff` | `up T = ⊥ ↔ ∀n, ¬T n` | 0 |
| `dichotomy_exclusive` | `¬(Halts T ∧ Stabilizes T)` | 0 |
| `dichotomy_double_neg` | `¬¬(Halts T ∨ Stabilizes T)` | 0 |

The operator `up` is a closure operator (monotone, idempotent, extensive) whose kernel characterizes the Π₁ side of the dichotomy. This characterization is algebraic: membership in ker(up) is equivalent to the universal negative statement `∀n, ¬T n`.

### 2. Classical Boundary (Zero Axioms for Equivalences)

**Source Localization.**

```lean
theorem stage_zero_is_em :
    (∀ T : Trace, HaltsUpTo T 0 ∨ StabilizesUpTo T 0) ↔ (∀ P : Prop, P ∨ ¬P)
```

Even at stage 0 (the smallest finite ordinal), quantifying over arbitrary traces `ℕ → Prop` yields EM. The source of classical content is the **class of traces** (Prop-valued), not the ordinal passage from finite to ω.

**Ordinal Gap Isolation.**

```lean
def LPOBool : Prop := ∀ f : ℕ → Bool, (∃ n, f n = true) ∨ (∀ n, f n = false)

theorem LPOBool_iff_LPOProp : LPOBool ↔ LPOProp
```

On decidable traces (`ℕ → Bool`), the passage from finite stages to ω yields LPO (Limited Principle of Omniscience), which is strictly weaker than EM in constructive mathematics.

**Two Distinct Sources.**

| Source | Transition | Principle | Strength |
|--------|------------|-----------|----------|
| Class | `ℕ → Bool` to `ℕ → Prop` | EM | Full classical |
| Ordinal | Finite to ω (decidable traces) | LPO | Weaker |

### 3. Abstract Schema

```lean
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  O : X → X
  mono : Monotone O
  idem : ∀ x, O (O x) = O x
  Sig : X → Prop
  sig_invar : ∀ x, Sig (O x) ↔ Sig x
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x
```

A dichotomy is **structural** when:
1. An operator O with closure properties exists
2. The signal Sig is preserved by O
3. The negative side is characterized as ker(O)

**Derived Theorems.**

| Theorem | Statement | Axioms |
|---------|-----------|--------|
| `sig_imp_ne_bot` | `Sig x → O x ≠ ⊥` | 0 |
| `ne_bot_imp_notnot_sig` | `O x ≠ ⊥ → ¬¬Sig x` | 0 |
| `ne_bot_imp_sig` | `O x ≠ ⊥ → Sig x` | Classical |

The passage from `¬¬Sig x` to `Sig x` is precisely where EM enters.

**Instantiation.**

```lean
def traceSD : StructuralDichotomy Trace where
  O := up
  mono := up_mono
  idem := up_idem
  Sig := Halts
  sig_invar := exists_up_iff
  ker_iff := up_eq_bot_iff
```

### 4. Triptych (T1 / T2 / T3)

**T1 — Canonicity.**

```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T : Trace, Rev0_K K T ↔ Halts T
```

Any valid kit (one that correctly detects halting on monotone traces) yields exactly the standard halting predicate on all traces. The operator `up` normalizes arbitrary traces to monotone form.

**T2 — Uniform Barrier.**

```lean
theorem T2_impossibility {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K) :
    ¬ ∃ _ : InternalHaltingPredicate S K, True
```

No internal predicate can be simultaneously total, correct, complete, and r.e. This is derived from Kleene's Second Recursion Theorem via diagonal argument.

**T3 — Local Navigation.**

```lean
theorem T3_oracle_extension_explicit ... :
    ∃ S3 : Set PropT,
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      pick.p ∈ S3 ∧
      ¬ S.Provable pick.p
```

Given an external oracle providing the side (Halts or Stabilizes), sound corpus extension is possible. The barrier is uniformity (`∃H.∀e`), not instancewise certificates (`∀e.∃Sₑ`).

### 5. Abstract Dynamics

```lean
structure PickWorld (Index PropT : Type) where
  Truth : PropT → Prop
  pick : Index → PropT
  pick_true : ∀ i, Truth (pick i)
```

From any pick oracle, the following are derived:

| Theorem | Statement |
|---------|-----------|
| `chain_sound` | All chain states are sound |
| `lim_sound` | The limit is sound |
| `lim_schedule_free` | Under fair schedule: `lim = S₀ ∪ AllPicks` |
| `lim_eq_omegaState` | Limit equals canonical ω-state |
| `omegaState_minimal` | ω-state is minimal sound extension |

The dynamics is independent of Trace/up. It depends only on the abstract structure of picks with truth certificates.

**Bridge Construction.**

```lean
def pickWorldOfSDOracle {Index : Type} (elem : Index → X)
    (oracle : SDOracle D Index elem) :
    PickWorld Index Prop
```

No `noncomputable`, no `classical`. The oracle carries the certificate; the bridge merely extracts it.

---

## Interpretation

### What is Demonstrated

1. **Structural Independence.** The dichotomy structure (operator, kernel characterization, signal invariance) exists with zero axioms.

2. **EM as Evaluator.** The equivalence `dichotomy ↔ EM` is proven with zero axioms. EM is not presupposed; it is characterized as exactly the principle needed to evaluate the pre-existing structure.

3. **Source Localization.** The theorem `stage_zero_is_em` proves that classical content enters through the class of traces (`ℕ → Prop`), not through the ordinal passage. This is not a philosophical claim but a formal result.

### Implication for Foundational Systems

ZFC and Peano Arithmetic (with classical logic) do not **found** the dichotomy. They **evaluate** a partition that exists structurally without them.

The algebraic characterization `up T = ⊥ ↔ Stabilizes T` transforms a logical statement (universal negative) into an operator equation. The evaluation of which side holds requires EM, but the partition itself is prior.

---

## File Structure

### Base Layer

| File | Contents |
|------|----------|
| `Trace.lean` | `Trace`, `Halts`, `up`, `up_mono`, `exists_up_iff` |
| `Kit.lean` | `RHKit`, `DetectsMonotone`, `Rev0_K` |

### Theory Layer

| File | Contents |
|------|----------|
| `Canonicity.lean` | T1: `T1_traces`, `T1_uniqueness`, semantic bridge |
| `Impossibility.lean` | T2: `diagonal_bridge`, `T2_impossibility` |
| `Complementarity.lean` | T3: `OraclePick`, `S1Set`, `S3Set`, oracle extension |
| `Stabilization.lean` | `Stabilizes`, `KitStabilizes`, kernel link |
| `Categorical.lean` | `up` as coreflector, `CloE`, `Frontier` theorems |

### Abstract Layer

| File | Contents |
|------|----------|
| `StructuralDichotomy.lean` | Abstract schema, instantiation, EM/AC analysis |
| `AbstractDynamics.lean` | `PickWorld`, chain/limit, schedule invariance |
| `SD_Bridge.lean` | `pickWorldOfSDOracle`, no classical, no noncomputable |

### Boundary Layer

| File | Contents |
|------|----------|
| `OrdinalMechanical.lean` | `dichotomy_all_iff_em`, `stage_zero_is_em`, `LPOBool_iff_LPOProp` |
| `OrdinalBoundary.lean` | Constructive layer theorems, double negation |

---

## Axiom Verification

All structural theorems verify `#print axioms` as using zero axioms beyond Lean's kernel (propext, Quot.sound for equality reasoning where needed).

Key verifications:

```
#print axioms dichotomy_all_iff_em        -- []
#print axioms stage_zero_is_em            -- []
#print axioms LPOBool_iff_LPOProp         -- []
#print axioms up_eq_bot_iff               -- []
#print axioms traceSD                     -- [propext]
#print axioms T1_traces                   -- []
#print axioms T2_impossibility            -- []
```

Classical axioms appear only in:
- `dichotomy` (the affirmative dichotomy, not the equivalence)
- `ne_bot_imp_sig` (converting `¬¬Sig` to `Sig`)
- `sdpick_of_classical` (constructing picks from EM)

---

## Build

```bash
lake build
```

Requires Lean 4 with Mathlib.

---

## Summary

RevHalt formalizes the following chain of results:

1. `up T = ⊥ ↔ Stabilizes T` — The Π₁ side is algebraically characterized as ker(up)
2. `dichotomy_all_iff_em` — Total dichotomy is logically equivalent to EM
3. `stage_zero_is_em` — The source is the class (Prop), not the ordinal (ω)

**Conclusion.** Classical logic is a semantic evaluation capacity applied to a structure that exists independently. This is not an interpretation but the content of the theorems.