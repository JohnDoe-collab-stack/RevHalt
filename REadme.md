# RevHalt

Lean 4 (Mathlib) formalization of a "Reverse Halting" framework based on a central idea:

> **Monotonize any trace via a closure operator `up`, then impose a minimal correctness condition on Kits over monotone traces.**  
> This forces a **rigidity phenomenon (T1)**: the operator `Rev0_K` becomes *inevitably* equivalent to standard halting.

The project then establishes:
- **T1 (Canonicity)**: `Rev0_K` = `Halts` for any trace (under `DetectsMonotone`).
- **T2 (Impossibility)**: no uniform internalization (total/correct/complete + r.e.) of such a verdict exists (diagonalization/Kleene).
- **T3 (Complementarity)**: **sound** extensions exist **instance by instance** (quantifier swap), via external certificates / localized choices.
- **OracleMachine**: architecture making explicit where non-mechanical power resides (bridge/oracle), separated from the machine (PartRec).

---

## Mathematical Overview

### Traces and Halting

- **Trace**: `Trace := ℕ → Prop`
- **Halting**: `Halts (T : Trace) : Prop := ∃ n, T n`

### Monotone Closure `up`

```lean
def up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k
```

Intuition: `up T n` means "**T has been true at or before instant n**".

Two key facts (proved in `Base/Trace.lean`):

* `up T` is monotone.
* `∃n, up T n ↔ ∃n, T n` (exact preservation of existence).

### Kits and Minimal Structural Condition

A Kit:

```lean
structure RHKit where
  Proj : Trace → Prop
```

Condition **DetectsMonotone**:

```lean
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ ∃ n, X n)
```

Reading: the Kit is **forced to be standard on monotone traces** (but may be exotic elsewhere).

### Reverse Halting

```lean
def Rev_K (K : RHKit) (T : Trace) : Prop := K.Proj (up T)
abbrev Rev0_K := Rev_K
```

---

## Results (Theorems)

### T1 — Canonicity (Rigidity)

* `T1_traces`: for any trace `T`, if `DetectsMonotone K` then
  `Rev0_K K T ↔ Halts T`.
* `T1_uniqueness`: all valid Kits yield the same verdict on any trace.

Semantic version (`T1_semantics`): if a **bridge** links semantic consequence to `Halts (LR Γ φ)`, then the Kit verdict coincides with semantic consequence.

### T2 — Impossibility of Uniform Internalization (Diagonalization)

On `Nat.Partrec.Code`, we encode a constant "machine" trace:
`Machine c : Trace := fun _ => ∃ x, x ∈ c.eval 0`.

By combining:

* T1 (which identifies the verdict with halting),
* a diagonal bridge via Kleene `fixed_point₂`,
* and a minimal notion of internal system (`ImpossibleSystem`),

we obtain `T2_impossibility`: **no** internal predicate `H(e)` can be *uniformly* total + correct + complete (with the required r.e. semi-decidability).

### T3 — Complementarity (Non-Uniform Sound Extensions)

T3 constructs **corpora** (`Set PropT`) and proves their **external soundness** via a predicate `Truth : PropT → Prop`.

* One-sided frontier: `S1Set S encode_halt`
* Extension: `S3Set S S2 encode_halt := S2 ∪ S1Set ...`
* Two-sided local variant: `OraclePick` chooses `encode_halt e` or `encode_not_halt e` via a certificate, and extends by `S2 ∪ {pick.p}`.

### Quantifier Swap (Key to T2/T3 Coexistence)

* **Forbidden (T2)**: `¬ ∃H, ∀e, ...` (uniform)
* **Permitted (T3)**: `∀e, ∃Sₑ, ...` (instance by instance)

The project formalizes that these two forms coexist without contradiction: power is **localized** (certificates/choices) and **non-uniformizable**.

---

## What is "New" (Structural Explanation)

The novelty is not "an exotic Kit": **T1 shows this is impossible** once we impose correctness on monotone traces, because `Rev0_K` always passes through `up`.

The following sections develop this point precisely.

---

## Structural Notes (A–H)

### A. `up` is a Closure Operator (Reflection to Monotone Traces)

Definition:

```
(up T)(n)  ⟺  ∃ k ≤ n, T(k)
```

Structural properties:

1. **Extensive**: `T ≤ up T` (pointwise)
   `T(n) ⇒ (up T)(n)` by taking `k = n`.

2. **Monotone (as operator)**: if `T ≤ U` then `up T ≤ up U`.

3. **Idempotent**: `up(up T) = up T`.
   (Flattening an existential quantifier over `≤`.)

Conclusion: `up` is a **closure** projecting any trace onto its **canonical monotone version**.
In order/category language: it is a **reflection** into the subclass of monotone traces.

### B. `Halts` and `up`: Isolating the Σ₁ Content (Existence)

```
Halts(T) ⟺ ∃ n, T(n)
```

And the lemma:

```
(∃ n, up(T)(n)) ⟺ (∃ n, T(n))
```

Thus the closure `up` **exactly preserves** the existential content.

This is the reason everything "locks in" afterwards.

### C. `DetectsMonotone`: Correctness on Closed Objects

Axiom:

```
Monotone(X) ⇒ (K.Proj(X) ⟺ ∃ n, X(n))
```

Combined with A, this means: on **closed** traces (fixed points of `up`), the Kit cannot "invent".
The Kit is free only outside closed objects… but `Rev0_K` never gives it access to those cases.

### D. T1 = Unique Extension Along a Closure (Rigidity)

Definition:

```
Rev_K(T) := K.Proj(up T)
```

Since `up T` is monotone:

```
Rev_K(T) ⟺ ∃ n, up(T)(n) ⟺ ∃ n, T(n) ⟺ Halts(T)
```

Reading: **any** semantics `K.Proj` that is correct on closed objects, once precomposed with `up`,
becomes a unique invariant: existence.
Therefore, novelty cannot reside "in K".

### E. T2: Diagonalization = Impossibility of Uniformly Internalizing a Σ₁ Truth

On machines:

```
Machine(c)(n) ⟺ ∃ x, x ∈ c.eval(0)
```

so `Halts(Machine(c))` = "c converges".

T1 forces:

```
Rev(Machine(c)) ⟺ "c converges"
```

With Kleene SRT, we construct `e` such that:

```
Rev(e) ⟺ S ⊢ ¬H(e)
```

Then totality/correctness/completeness of `H` (plus minimal consistency) yields contradiction.

Reading: we do not use "code details", only

* an existential fact (Σ₁),
* a minimal r.e. hypothesis (to diagonalize),
* minimal consistency (to explode).

### F. T3: Complementarity = Non-Uniform Sound Extensions (Subtlety)

Here, T3 proves:

```
∀ p ∈ S₃, Truth(p)
```

Thus T3 concerns **corpora** (sets of true axioms), not yet a proof relation `Provable_{S₃}` deductively closed.
"Decision" is in the sense of: **adding the axiom** (membership), not: "uniform internal procedure".

* one-sided:
  ```
  S₁ = { encode_halt(e) | Rev(e) ∧ ¬(S ⊢ encode_halt(e)) }
  S₃ = S₂ ∪ S₁
  ```
* two-sided local: `OraclePick` carries the branch without decidability, and extends by `S₂ ∪ {p}`.

This is exactly `∀e, ∃` (certificate/extension), compatible with T2 (no uniform `∃`).

### G. Where is the Novelty at the Structural Level?

1. **T1 Rigidity** (canonicity via closure): neutralizes any "Kit power".
2. **Localization of non-mechanicity**: bridge/oracle/certificate/choice, and nowhere else.
3. **Quantifier swap** as a difference in logical strength: `∃H, ∀e` vs `∀e, ∃Sₑ`.
4. **Non-internalizable frontier**: `S₁` is indexed by a hard existential property (halting).

### H. Two Critical Points (To Be Aware Of)

1. **Deciding by axiom addition vs by deduction**: for "deciding in the proof-theoretic sense",
   one must define `Provable_{Sₑ}` (deductive closure of `S` + added axioms) and relate the rules to `Truth`.

2. **Infinity of the frontier**: `InfiniteS1` is a hypothetical structure;
   an "intrinsic" proof of infinity would require parameterized iteration/diagonalization.

---

## File Organization

* `RevHalt/Base/Trace.lean`: `Trace`, `Halts`, `up`, `up_mono`, `exists_up_iff`
* `RevHalt/Base/Kit.lean`: `RHKit`, `DetectsMonotone`, `Rev_K`, `Rev0_K`
* `RevHalt/Theory/Canonicity.lean`: T1, semantic bridge
* `RevHalt/Theory/Impossibility.lean`: T2 (Kleene SRT + diagonalization)
* `RevHalt/Theory/Complementarity.lean`: T3 (one-sided, strong, two-sided oracle)
* `RevHalt/Theory/QuantifierSwap.lean`: T2/T3 coexistence via quantifier swap
* `RevHalt/Theory/OracleMachine.lean`: a/o/c-machine architecture, T2 barrier

---

## Building / Verifying

Prerequisites: Lean 4 + Mathlib (via `lake`).

```bash
lake build
```

To verify a specific file:

```bash
lake env lean RevHalt/Theory/Canonicity.lean
```

---

## License / Contribution

Add your license (MIT/BSD/etc.) and contribution conventions here as needed.
