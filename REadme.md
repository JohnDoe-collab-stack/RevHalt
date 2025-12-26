# RevHalt Framework Theory

## Guiding Principle

RevHalt clearly factorizes oracles (truth, compilation, procedure, negative r.e., two-sided decision) and proves a **rigidity principle**: once normalized by `up`, all procedures satisfying a minimal contract coincide on the verdict. Incompleteness is not bypassed; it is reconfigured into a complementarity of **internal proof + stable external certification**.

The RevHalt framework introduces a **stable operational reference frame** to link:

1. **Semantic Truth** (models/satisfaction),
2. **Dynamics** (trace-based processes),
3. **Procedure** (a abstract "Kit"/observer),
4. **Internalization Limit** (internal provability à la Gödel).

The goal is not to "make Halting decidable", but to **make operativity independent of internal incompleteness** by clearly separating these layers and stabilizing their interaction.

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

This normalization is the mechanism that "stabilizes" exotic behaviors possible on non-monotone traces.

---

## 2) Procedural Layer: Kits and Rev Operator

### Kit (Abstract Observer)

A Kit is an observation mechanism:

* `RHKit` contains `Proj : Trace → Prop`

### Minimal Contract: `DetectsMonotone`

A Kit is **valid** if it is correct on monotone traces:

* `DetectsMonotone K := ∀ X, Monotone X → (K.Proj X ↔ ∃ n, X n)`

This contract forces **nothing** on non-monotone traces: freedom exists but is neutralized by `up`.

### Rev Operator

The canonized procedural verdict:

* `Rev_K K T := K.Proj (up T)` (alias `Rev0_K`)

`Rev` adds no "extensional truth" beyond `Halts`, but provides an **injection point** for procedures (solver, AI, oracle, engine, etc.) under a stability contract.

---

## 3) T1 — Canonicity: Inter-Procedural Stability

### T1 (Traces)

Under `DetectsMonotone K`, for any trace:

* `Rev0_K K T ↔ Halts T`

The canonicity is obtained by (i) a **minimal contract on monotones** (`DetectsMonotone`) and (ii) a **monotone normalization** (`up`) that forces every input into this domain.

### Corollary (Uniqueness)

Two valid Kits always yield the same verdict:

* `Rev0_K K1 T ↔ Rev0_K K2 T`

**Foundational Sense:** Operativity is "plug-and-play": different mechanisms can be plugged in, and as long as they respect the minimal contract (on monotones), the verdict becomes **canonical**.

---

## 4) Semantic Bridge: Making Semantics "Dynamic"

### External Semantics

We fix:

* `Sat : Model → Sentence → Prop`

We define semantic consequence via model/theory closure:

* `ModE Γ := {M | ∀ φ ∈ Γ, Sat M φ}`
* `ThE K := {φ | ∀ M ∈ K, Sat M φ}`
* `CloE Γ := ThE (ModE Γ)`
* `SemConsequences Γ φ := φ ∈ CloE Γ`

### Local Reading `LR`

We introduce a local compilation:

* `LR : Set Sentence → Sentence → Trace`

### Bridge Hypothesis

* `DynamicBridge Sat LR := ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)`

### Procedural Verdict on a Pair (Γ, φ)

* `verdict_K LR K Γ φ := Rev0_K K (LR Γ φ)`

### T1 (Semantics)

For any semantics that admits an `LR` satisfying `DynamicBridge`:

* `SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ`

**Sense:** Semantics become **dynamic** via `LR`, then **operationally stable** via `Rev` and T1.

---

## 5) T2 — Impossibility: The Internalization Barrier

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

**Sense:** The canonical (procedural) verdict cannot be "absorbed" into a total internal decider. Operativity must remain **external/complementary**, not totalized in `Provable`.

---

## 6) T3 — Complementarity: Non-Internalizable but Sound Frontier

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

**Sense:** Instead of suffering incompleteness as a loss of operativity, we organize it into **complementarity**: internal proof (`S2`) + certifiable frontier (`S1`) + sound extensions (`S3`).

---

## 7) Where is the "Oracle" in the Framework?

The framework does not hide the oracle: it **factorizes** it.

* **Truth Oracle**: `Sat` / `Truth`
* **Compilation/Measure Oracle**: `LR` + `DynamicBridge`
* **Procedural Oracle**: `K.Proj` (stabilized by `up` + T1)
* **Negative R.E. Oracle**: `f` (semi-decidability used to diagonalize)
* **Two-Sided Decision Oracle**: `OraclePick`

This decomposition is precisely what makes the framework "surgical": every dependency is typed and localized.

---

## Summary

RevHalt is not a new definition of `Halts`: it is a **foundational stability framework** that transforms semantic truths into dynamics (via `LR`), stabilizes heterogeneous procedures (via `up` + T1), proves the internalization limit (T2), and organizes incompleteness into sound complementarity (T3).
