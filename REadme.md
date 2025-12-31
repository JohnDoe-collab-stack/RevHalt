Oui — j’ai **condensé** (réduction de redondances + regroupement), donc il y a eu **moins de lignes**. Mais l’objectif n’était pas de “supprimer l’idée”, plutôt de **préserver le contenu** en corrigeant les points de formulation qui pouvaient être factuellement trop forts ou ambigus (surtout autour de “0 axiomes”, “au-delà du kernel”, et “source” vs “localisation de dépendance”).

Si tu veux **une version longue** qui garde pratiquement toute ta structure et tes sections, voici une réécriture **beaucoup plus proche de ton texte**, avec corrections minimales mais précises (prête à coller).

---

## RevHalt

RevHalt is a Lean 4 (Mathlib) formalization that **localizes** the logical strength required to obtain *global dichotomies*, and separates it from the **structural content** that forces certificate shape (kernel vs signal) via an operator.

> Key point: RevHalt does **not** “assume EM as a foundation” inside the key equivalences; instead it **characterizes** EM (and LPO) as exactly the evaluation principles needed to assert certain total dichotomies, while the operator/kernel/signal facts are proved structurally.

## Main Result

**Theorem (characterization).** The total dichotomy for Prop-valued traces is logically equivalent to the Law of Excluded Middle:

```lean
theorem dichotomy_all_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬P)
```

* In your OrdinalMechanical development, the **equivalence proof** is verified by `#print axioms` as axiom-free (`[]`) in the usual Lean sense (“no additional axioms are used by that proof term”).
* This theorem should be stated as: **EM is exactly the strength of the total dichotomy** over `Trace := ℕ → Prop`.

**Corollary (properly phrased).** The *structural partition mechanism* (operator, kernel characterization, signal invariance) is established independently of EM; EM is needed only when one demands **positive branch selection** or a **global disjunction** at the level of propositions.

---

## Formal Content

### 1. Primitive Layer (structural facts)

**Definitions.**

```lean
def Trace := ℕ → Prop
def Halts (T : Trace) : Prop := ∃ n, T n                    -- Σ₁
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n            -- Π₁
def up (T : Trace) : Trace := fun n => ∃ k, k ≤ n ∧ T k    -- Cumulative closure
```

**Structural theorems** (in your base/theory files, these are in the “no EM needed” regime; `#print axioms` typically reports `[]` for them):

| Theorem         | Statement                         | Comment on axioms       |
| --------------- | --------------------------------- | ----------------------- |
| `up_mono`       | `Monotone (up T)` (or order-form) | structural              |
| `up_idem`       | `up (up T) = up T`                | structural              |
| `exists_up_iff` | `(∃n, up T n) ↔ (∃n, T n)`        | signal invariance       |
| `up_eq_bot_iff` | `up T = ⊥ ↔ ∀n, ¬T n`             | kernel characterization |

**Meaning.** `up` acts like a closure/coreflection to monotone traces; the Π₁-side is captured as a **kernel condition** (`up T = ⊥`), not merely as an opaque negation.

> Caution (wording): say “proved without EM” / “structural” rather than “beyond Lean’s kernel” globally, because imports may bring in standard axioms; `#print axioms` is the correct *per-theorem* audit tool.

---

### 2. Boundary (where EM/LPO appear)

#### 2.1 Class gap (Prop-valued traces)

**Stage 0 localization.**

```lean
theorem stage_zero_is_em :
    (∀ T : Trace, HaltsUpTo T 0 ∨ StabilizesUpTo T 0) ↔ (∀ P : Prop, P ∨ ¬ P)
```

This is a *sharp localization statement*: once you quantify over `Trace := ℕ → Prop`, even the weakest finite stage already recovers EM (via constant traces `constTrace : Prop → Trace`).

So the “classical content” is not coming from ω here; it is coming from the **Prop-valued trace class**.

#### 2.2 Ordinal gap (ω on decidable sequences)

For decidable data, the ω-step corresponds to LPO:

```lean
def LPOBool : Prop :=
  ∀ f : ℕ → Bool, (∃ n, f n = true) ∨ (∀ n, f n = false)
```

and you connect Bool-vs-decidable-predicate presentations:

```lean
theorem LPOBool_iff_LPOProp : LPOBool ↔ LPOProp
```

**Interpretation.** On decidable traces, the finite-stage checks are constructive, but the passage to an ω-total dichotomy is exactly the LPO-type omniscience step.

#### 2.3 Two distinct loci (precise statement)

| Locus       | What changes                            | Principle |
| ----------- | --------------------------------------- | --------- |
| **Class**   | `ℕ → Bool` / decidables → `ℕ → Prop`    | EM        |
| **Ordinal** | finite stages → ω (decidable sequences) | LPO       |

And in constructive mathematics: **EM ⇒ LPO**, while LPO is strictly weaker than EM.

---

### 3. Abstract Schema (StructuralDichotomy)

```lean
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  O : X → X
  mono : Monotone O
  idem : ∀ x, O (O x) = O x
  Sig : X → Prop
  sig_invar : ∀ x, Sig (O x) ↔ Sig x
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x
```

**Derived theorems (correct dependency phrasing).**

| Theorem                 | Statement           | Dependency profile                                         |
| ----------------------- | ------------------- | ---------------------------------------------------------- |
| `sig_imp_ne_bot`        | `Sig x → O x ≠ ⊥`   | structural                                                 |
| `ne_bot_imp_notnot_sig` | `O x ≠ ⊥ → ¬¬Sig x` | structural                                                 |
| `ne_bot_imp_sig`        | `O x ≠ ⊥ → Sig x`   | needs an evaluation principle like `¬¬P → P` (EM suffices) |

**Where EM enters (precisely).** The only genuinely “classical” jump in this micro-logic is upgrading `¬¬Sig` to `Sig` (or equivalently asserting a total decidability/dichotomy at the Prop level).

**Instantiation (Trace/up).**

```lean
def traceSD : StructuralDichotomy Trace where
  O := up
  mono := up_mono
  idem := up_idem
  Sig := Halts
  sig_invar := exists_up_iff
  ker_iff := up_eq_bot_iff
```

---

### 4. Triptych (T1 / T2 / T3)

(Keeping your intent; these are “project-level results” not reducible to the ordinal boundary file.)

**T1 — Canonicity.**

```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T : Trace, Rev0_K K T ↔ Halts T
```

Meaning: under the weak detection hypothesis, “kits” collapse to the canonical Σ₁ signal; structure forces the certificate semantics.

**T2 — Uniform Barrier.**

```lean
theorem T2_impossibility ... :
    ¬ ∃ _ : InternalHaltingPredicate S K, True
```

Meaning: no uniform internal predicate can be total+correct+complete+r.e.; the obstruction is *uniformity*.

**T3 — Local Navigation.**

Instancewise, certificates exist (`∀e, ∃Sₑ`), and sound extension is possible given an external oracle of side/picks; the barrier remains the uniform swap (`∃H, ∀e`).

---

### 5. Abstract Dynamics (PickWorld)

```lean
structure PickWorld (Index PropT : Type) where
  Truth : PropT → Prop
  pick : Index → PropT
  pick_true : ∀ i, Truth (pick i)
```

From this, you derive (schematically):

* soundness (`chain_sound`, `lim_sound`)
* closed forms (`lim_closed_form`)
* schedule-independence under fairness (`lim_eq_of_fair_schedules`)
* canonical ω-state (`omegaState`) and minimality (`omegaState_minimal`)

**Bridge construction (important phrasing).** The bridge can be “no classical/no noncomputable” *when the oracle already carries certificates*. The bridge itself is then purely structural extraction.

---

## Interpretation (tight, non-overreaching)

What is mechanically demonstrated is a **dependency localization**:

1. The operator/kernel/signal machinery is proved structurally (no need to assume EM to state or prove the kernel/signal lemmas).
2. The statement “for all Prop-valued traces, `Halts T ∨ Stabilizes T`” is **equivalent to EM** (so demanding that total dichotomy is exactly demanding EM-strength evaluation).
3. Restricting to decidable sequences isolates **LPO** at the ω-step.

So: classical principles appear as **evaluation strength requirements** for certain global disjunctions, while the “certificate geometry” is forced by structure.

---

## Axiom Verification (correct phrasing)

* `#print axioms` audits **each theorem term**.
* It is correct to write things like:

```
#print axioms dichotomy_all_iff_em   -- []
#print axioms stage_zero_is_em       -- []
#print axioms LPOBool_iff_LPOProp    -- []
#print axioms up_eq_bot_iff          -- []
```

* It is also important to acknowledge that other parts of the architecture (e.g. involving `OracleMachine`, quotients, extensionality) may legitimately show:

`[propext, Classical.choice, Quot.sound]`

This does not invalidate the separation; it just means the separation must be stated as **per-theorem localization**, not as “the entire environment is 0-axiom”.

---

Si tu veux, je peux aussi produire une **version “diff”** (ligne à ligne) entre ton texte et cette correction, pour que tu voies exactement où j’ai changé une formulation et pourquoi (principalement: éviter les sur-assertions globales et rendre les claims compatibles avec les sorties `#print axioms` que tu montres).
