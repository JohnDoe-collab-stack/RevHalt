# RevHalt Framework Theory

## Guiding Principle

RevHalt is **foundational** in the sense of *clarifying structure and dependencies*, not in the sense of providing new decision power.

### What is foundational here

* **Clean separation of layers:**
  Dynamic (`Trace`, `Halts`, `up`) / Procedure (`Kit`, contract) / Semantic (`Sat`, `CloE`) / Internalization limit (Gödel/T2).
  The reader is forced to see *where* each hypothesis lives.

* **Rigidity as normalization:**
  `up` + "correct on monotones" ⇒ all admissible mechanisms collapse to the same verdict.
  This is an *operational reference frame*: exotic procedures outside the domain are neutralized by `up`.

* **Explicit oracle localization:**
  The power is not hidden in `Rev`. It is in the *bridge* (`LR` + `DynamicBridge`) and in diagonalization hypotheses for T2/T3.

* **Complementarity, not bypass:**
  Incompleteness is not evaded — it is organized into a frontier of "true (certified) but unprovable" + sound extensions.

### What is NOT claimed

* T1 does **not** give an effective decision procedure.
* `Rev0_K` does **not** provide truth beyond `Halts` without external hypotheses.
* The framework **does not bypass** incompleteness.

### Core axis: Dependency → Typing → Localization

The framework's value is making explicit: *what depends on what*, and *where incompleteness enters*.

---

## 1) Dynamic Layer: Traces, Halting, Normalization

### Traces

A **trace** is a logical process:

* `Trace := ℕ → Prop`
* Intuition: `T n` means "at step n, the property is reached".

### Halting (Minimal Specification)

* `Halts T := ∃ n, T n`

### Monotone Normalization (`up`)

We transform any trace into a **cumulative** (monotone) trace:

* `up T n := ∃ k ≤ n, T k`
* Properties:
  * `up_mono : Monotone (up T)`
  * `exists_up_iff : (∃ n, up T n) ↔ (∃ n, T n)`

This normalization is the mechanism that **neutralizes** exotic procedural behavior on non-monotone traces by forcing every input into a monotone domain.

### Typing: `Prop` vs `PropT`

* `Prop` = meta-level truth (external, Lean's `Prop`)
* `PropT` = object-level sentences (coded statements in an internal formal system)
* `Provable : PropT → Prop` lives at the interface between the two levels

---

## 2) Procedural Layer: Kits and Rev Operator

### Kit (Abstract Observer)

A Kit is an observation mechanism:

* `RHKit` contains `Proj : Trace → Prop`

### Minimal Contract: `DetectsMonotone`

A Kit is **valid** if it is correct on monotone traces:

* `DetectsMonotone K := ∀ X, Monotone X → (K.Proj X ↔ ∃ n, X n)`

This is a **strong** condition: it imposes **exact equivalence** with `∃ n` on every monotone trace. This is precisely what makes T1 inevitable.

> **Note:** `DetectsMonotone` fixes `Proj` entirely on the image of `up`; `Rev0_K` merely restricts the domain of application to this image.

### Rev Operator

The canonized procedural verdict:

* `Rev_K K T := K.Proj (up T)` (alias `Rev0_K`)

Under `DetectsMonotone`, `Rev0_K` adds no "extensional truth" beyond `Halts`, but provides an **injection point** for procedures (solver, AI, oracle, engine, etc.) under a stability contract.

---

## 3) T1 — Canonicity: Inter-Procedural Stability

### T1 (Traces)

Under `DetectsMonotone K`, for any trace:

* `Rev0_K K T ↔ Halts T`

The canonicity is obtained by (i) a **minimal contract on monotones** (`DetectsMonotone`) and (ii) a **monotone normalization** (`up`) that forces every input into this domain.

### Corollary (Uniqueness)

Two valid Kits always yield the same verdict:

* `Rev0_K K1 T ↔ Rev0_K K2 T`

**Why this works:** `DetectsMonotone` demands *full extensional correctness* on monotone traces — i.e., exact equivalence with `∃ n`. Then `up` maps everything into that fragment. So T1 is inevitable: it is a **closure-induced extensional collapse**.

**Foundational Sense:** Operativity is "plug-and-play": different mechanisms can be plugged in, and as long as they respect the minimal contract (on monotones), the verdict becomes **canonical**.

> **Key points:**
> * **T1 is a closure lemma:** correctness on closed points (monotones) + closure `up` ⇒ rigidity of verdict.
> * **T1 adds no power beyond `Halts`** — it stabilizes heterogeneous procedures under a contract.
> * **The power is elsewhere:** in `LR`, in `DynamicBridge(Sat, LR)`, and in diagonalization hypotheses (for T2/T3).

> **Note:** `Rev0_K` is a *semantic equivalence* to `Halts`, not a computable decision method. Any computability lives in how a concrete `K.Proj` is realized.

---

## 4) Semantic Bridge: Making Semantics "Dynamic"

### External Semantics

We fix:

* `Sat : Model → Sentence → Prop`

We define semantic consequence via model/theory closure:

* `ModE Sat Γ := {M | ∀ φ ∈ Γ, Sat M φ}`
* `ThE Sat 𝕄 := {φ | ∀ M ∈ 𝕄, Sat M φ}` (note: 𝕄 is a class of models, distinct from Kit `K`)
* `CloE Sat Γ := ThE Sat (ModE Sat Γ)`
* `SemConsequences Sat Γ φ := φ ∈ CloE Sat Γ`

### Local Reading `LR`

We introduce a local compilation:

* `LR : Set Sentence → Sentence → Trace`

### Bridge Hypothesis

* `DynamicBridge Sat LR := ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)`

### Procedural Verdict on a Pair (Γ, φ)

* `verdict_K LR K Γ φ := Rev0_K K (LR Γ φ)`

### T1 (Semantics)

For any semantics that admits an `LR` satisfying `DynamicBridge`, and any `K` satisfying `DetectsMonotone`:

* **Hypotheses:** `DynamicBridge Sat LR` **and** `DetectsMonotone K`
* **Conclusion:** `SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ`

**Sense:** Semantics become **dynamic** via `LR`, then **operationally stable** via `Rev` and T1.

---

## 5) Categorical Structure: Two Worlds, Two Closures

The framework operates in **two distinct worlds**:

| World | Objects | Closure Operator |
|-------|---------|------------------|
| **Dynamic** | Traces (`ℕ → Prop`) | `up` — monotonizes a trace |
| **Semantic** | Theories (`Set Sentence`) | `CloE` — closes under logical consequence |

Each world has its own closure:

* In **traces**: `up T n := ∃ k ≤ n, T k` (cumulative/monotone)
* In **sentences**: `CloE Γ := ThE (ModE Γ)` (semantic closure)

Both satisfy: **extensive** (Γ ⊆ closure(Γ)), **monotone** (Γ ⊆ Δ → closure(Γ) ⊆ closure(Δ)), **idempotent** (closure(closure(Γ)) = closure(Γ)).

**Why this matters:** The two worlds are independent. To connect them, we need a **bridge**.

---

## 6) Bridge Conditions: Connecting the Two Worlds

The bridge is `LR : Set Sentence → Sentence → Trace`. It compiles a semantic question (Γ, φ) into a trace.

**The key question:** Does `LR` respect both closures?

The answer is the **commutation condition**:

```
up (LR Γ φ) = LR (CloE Γ) φ
```

**What this means:** 
* Closing the theory first (`CloE`), then compiling (`LR`)
* OR compiling first (`LR`), then normalizing the trace (`up`)
* **Both paths give the same result.**

```
Theories ──CloE──► Closed Theories
    │                    │
   LR                   LR
    ▼                    ▼
Traces ────up────► Monotone Traces
```

**Consequence:** The verdict `Rev0_K K (LR Γ φ)` depends only on `CloE Sat Γ`, not on the syntactic presentation of Γ.

**Structural interpretation:** This is the natural condition (closure morphism) ensuring that compilation is insensitive to the syntactic presentation of Γ. The *usage* here — connecting trace-level closure to semantic closure via a typed bridge — is what characterizes this framework.

> **Note:** The equality `up (LR Γ φ) = LR (CloE Sat Γ) φ` is **strong** (extensional equality of traces). If you only need verdict invariance, a weaker condition suffices: `Halts(LR Γ φ) ↔ Halts(LR (CloE Sat Γ) φ)`.

---

## 7) T2 — Impossibility: The Internalization Barrier

### Concrete Computation Model

We take `Nat.Partrec.Code` and a "Machine" trace:

* `Machine c : Trace := fun _ => ∃ x, x ∈ c.eval 0`
* Thus `Halts (Machine c) ↔ c converges on 0`

### Diagonal Bridge

We fabricate a code `e` such that:

* `Rev0_K K (Machine e) ↔ target e`

The fixed point (SRT) serves as an ingredient, but the diagonal statement applies to `Rev0_K` (the canonical verdict), not directly to `eval`.

### Minimal Internal System

`ImpossibleSystem` formalizes:

* `Provable`, `Not`, `FalseT`, consistency, explosion.

### Result

There exists no internal predicate `H e` that is simultaneously:

* **Total** (the system proves `H e` or `¬H e`),
* **Correct and Complete** with respect to `Rev0_K`,
* and **Semi-Decidable** on `Provable (¬H e)`.

> **Why semi-decidability?** This hypothesis makes the diagonal attack *effective in the meta-reasoning*: it allows enumerating proofs of `¬H e` (r.e. of `Provable`), which is needed to construct the fixed-point code `e*`.
>
> **Operationally:** There exists a partial recursive `f(e)` that halts iff `Provable(¬H e)`. This is the standard ingredient for effective diagonalization.

**What T2 really says:** This is a Rice/Gödel style diagonalization aimed at any internal total predicate trying to coincide with `Rev0_K` on machine traces. Since `Rev0_K K (Machine e) ↔ Halts(Machine e)` (by T1), "internalizing Rev0" is just "internally deciding halting."

The barrier is not an artifact of the Kit layer — it is the standard internalization impossibility resurfacing *after* the normalization/canonicity step.

**Sense:** The canonical verdict cannot be absorbed into a total internal decider. Operativity must remain **external/complementary**, not totalized in `Provable`.

---

## 8) T3 — Complementarity: Non-Internalizable but Sound Frontier

We fix:

* An internal corpus `S2 : Set PropT` with external soundness `h_S2_sound : p∈S2 → Truth p`,
* A translation `encode_halt : Code → PropT`.

### Frontier S₁ (One-Sided)

* `S1Set := { encode_halt e | Rev0_K K (Machine e) ∧ ¬ Provable(encode_halt e) }`

The frontier is not "independence in the model-theoretic sense", it is "certified (external) but unprovable (internal)".

### Complementary Extension

* `S3Set := S2 ∪ S1Set`

### T3.1 (Sound Extension)

Under encoding correctness hypotheses:

* `S3` extends `S2`, remains sound (w.r.t `Truth`),
* and contains statements that are **certified** but **unprovable**.

### T3.2 (Disjoint Families)

With infinitely many S₁ witnesses + index partition, we construct a family `{S3_n}` of sound extensions, disjoint on the added part.

### Two-Sided Oracle Variant

`OraclePick` explicitly encapsulates the "halt / not halt" choice without internal decidability, enabling a local sound extension `S2 ∪ {pick.p}`.

> **Note**: Locally, we assume `pick`. Globalizing this into a function `e ↦ pick(e)` would require a form of decision (classical/Decidable) or an external oracle.

**What T3 requires (meta-assumptions):**

1. `encode_halt` is truth-preserving: `Truth(encode_halt e) ↔ Halts(Machine e)`
2. The base corpus is externally sound: `Provable p → Truth p`
3. The internal system is **recursively axiomatized** (r.e.)
4. The system has **enough arithmetic strength** (Σ1-representability of computation)
5. **Σ1-soundness** (or stronger) to ensure existence of true-but-unprovable halts

**Sense:** Instead of suffering incompleteness as a loss of operativity, we organize it into **complementarity**: internal proof (`S2`) + certifiable frontier (`S1`) + sound extensions (`S3`).

---

## 9) Where is the "Oracle" in the Framework?

The framework does not hide the oracle: it **factorizes** it.

* **Truth Oracle**: `Sat` / `Truth`
* **Compilation/Measure Oracle**: `LR` + `DynamicBridge`
* **Procedural Oracle**: `K.Proj` (stabilized by `up` + T1)
* **Negative R.E. Oracle**: `f` (semi-decidability used to diagonalize)
* **Two-Sided Decision Oracle**: `OraclePick`

This decomposition is precisely what makes the framework "surgical": every dependency is typed and localized.

---

## Summary

RevHalt is not a new definition of `Halts`: it is a **canonicalization mechanism** that:

* Transforms semantic truths into dynamics (via `LR`),
* Stabilizes heterogeneous procedures (via the closure `up` + T1),
* Proves the internalization limit (T2),
* Organizes incompleteness into sound complementarity (T3).

---

## What is Proved vs What is Assumed

### Proved (purely from definitions)

| Result | Statement |
|--------|-----------|
| **T1 (traces)** | `Rev0_K K T ↔ Halts T` for any `K` satisfying `DetectsMonotone` |
| **T1 (uniqueness)** | All valid Kits coincide on all traces |

### Assumed (structural conditions on LR)

| Assumption | Role |
|------------|------|
| `DynamicBridge(Sat, LR)` | Semantic-to-dynamic equivalence — the "oracle" is here |
| `LR_commutes_with_closure` | Ensures verdict depends only on `CloE Sat Γ` (strong structural assumption) |
| Computability claims on `LR` or `K` | Not provided by the framework |

### Proved (given structural assumptions + meta-assumptions)

| Result | Requires |
|--------|----------|
| **Verdict invariance** | `LR_commutes_with_closure` + `DetectsMonotone K` |
| **T2** | Sound r.e. theory + diagonalization (Kleene fixed point) |
| **T3** | r.e. axiomatization + Σ1-representability + Σ1-soundness |

---

## Core Insight

`Rev0_K` is **not** a new capability or decision procedure. It is a **closure-induced canonicalization**: by precomposing any `Proj` with `up` and requiring correctness only on the monotone subdomain, all admissible procedures become extensionally equal.

### Core Lemma (Closure Canonicalization)

**Abstract form:**
* Let `C` be a closure operator (extensive, monotone, idempotent).
* Let `P` be any predicate that is *correct on closed points*: `∀ X, Closed(X) → (P X ↔ ∃ n, X n)`.
* Then `P ∘ C` is unique and equals the existential.

**Instantiation in RevHalt:**
* `C = up` (closure on traces)
* `P = K.Proj` with `DetectsMonotone K` (correct on monotones = closed points)
* Conclusion: `Rev0_K K T = K.Proj (up T) ↔ Halts T`

This makes the "closure-induced collapse" structure immediately visible.

---

The abstraction:

* `up` is a **closure operator** on traces,
* `DetectsMonotone` requires correctness on the **closed subdomain**,
* `Rev0_K` is **evaluation after closure**,
* All valid Kits agree because `up` forces every input into the domain where the contract pins `Proj` down.

Incompleteness is not bypassed — it is **isolated** into the bridge (`LR`, `DynamicBridge`) and into internalization constraints (T2).
