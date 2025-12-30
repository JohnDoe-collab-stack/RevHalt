# RevHalt

RevHalt is a Lean 4 (Mathlib) formalization of a single idea:

**Turn an impossibility (undecidability of halting) into a navigable structure.**

---

## Why is this original?

### Gödel/Turing vs RevHalt

| Approach | Result | Character |
|----------|--------|-----------|
| **Gödel/Turing** | "There exist true but unprovable statements" | Existence theorem (static) |
| **RevHalt** | "Here is the dynamics of navigating incompleteness" | Process (dynamic) |

Gödel and Turing prove that limits exist. RevHalt provides a **formal dynamics** on those limits:

1. **T1 (Rigidity)**: What is structurally fixed — any valid observer collapses to standard halting
2. **T2 (Barrier)**: What is uniformly impossible — no internal predicate can decide all instances
3. **T3 (Navigation)**: What is locally possible — certificate-carried extensions, step by step

Incompleteness becomes **navigable**: not a wall, but a structured space with typed certificates.

### Π₁ Stabilization as First-Class Certificate

Standard computability treats "doesn't halt" as `¬∃n. T n` — a **logical negation** of Σ₁.

RevHalt treats "stabilizes" as `∀n. ¬T n` — a **first-class Π₁ structure**:

| Approach | Form | Status |
|----------|------|--------|
| Standard | `¬∃n. T n` | Negation (derived) |
| RevHalt | `∀n. ¬T n` | Π₁ certificate (primitive) |

The Kit's negative verdict `¬Rev0_K` becomes a **typed Π₁ certificate** that can be:
- **Carried** by `OraclePick` on the "stabilization" branch
- **Used** as fuel for sound extensions in T3
- **Linked** algebraically to the kernel of `up`: `up T = ⊥ ↔ ∀n. ¬T n`

Stabilization is not "we don't know if it halts" — it is a **positive geometric structure** extracted from the instrument.

---

## Categorical Structure

RevHalt exposes **two parallel operator structures**:

### 1) `up` as Coreflector (Traces)

The operator `up : Trace → Trace` is the coreflection into monotone traces:

```lean
up T ≤ X ↔ T ≤ X    (for monotone X)
```

Properties:
- **Idempotent**: `up (up T) = up T`
- **Signal-preserving**: `Halts (up T) ↔ Halts T`
- **Kernel = Stabilization**: `up T = ⊥ ↔ ∀ n, ¬ T n`

The operator `up` acts as a **projector/filter**: it preserves signals (Halts) and annihilates noise (Stabilizes to ⊥).

### 2) `CloE = ThE ∘ ModE` as Closure (Sentences)

For sentences/models:

```lean
ModE Sat Γ := { M | ∀ φ ∈ Γ, Sat M φ }
ThE K := { φ | ∀ M ∈ K, Sat M φ }
CloE := ThE ∘ ModE
```

Properties:
- **Galois connection**: `K ⊆ ModE Γ ↔ Γ ⊆ ThE K`
- **Closure operator**: `CloE` is extensive, monotone, idempotent

### 3) Frontier Anti-Monotonicity

The **frontier** S1(S2) = { p | Truth p ∧ ¬Provable S2 p } is anti-monotone:

```lean
S2 ⊆ S2' → Frontier(S2') ⊆ Frontier(S2)
```

More you prove ⟹ smaller the frontier. Extensions shrink the "unknown".

**Divergence witness**: If two theories prove different things, their frontiers become incomparable:

```lean
(A proves p, B doesn't) ∧ (B proves q, A doesn't) → Frontiers(A) ⊄ Frontiers(B) ∧ vice versa
```

---

## Architecture: Kernel + State

RevHalt separates two concerns:

| Layer | Object | Meaning |
|-------|--------|---------|
| **Kernel** (fixed) | `S.Provable : PropT → Prop` | Internal derivability |
| **State** (variable) | `S2, S3 : Set PropT` | Accepted/certified truths |

**Key invariant**: `¬ S.Provable p` is absolute — p remains unprovable regardless of corpus extensions.

T2 blocks uniform decision **in the calculus**.  
T3 permits instancewise extension **in the corpus**.

---

## Core Objects

### Traces and halting

```lean
Trace := ℕ → Prop
Halts (T : Trace) : Prop := ∃ n, T n
```

### The monotone closure `up`

```lean
up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k
```

### Algebraic Stabilization

```lean
up T = ⊥ ↔ ∀ n, ¬ T n
```

Stabilization is **structural nullity** — the trace collapses to the zero element under the projector.

### Kits and validity

```lean
structure RHKit where
  Proj : Trace → Prop

DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ Halts X)
```

### Reverse halting

```lean
Rev0_K (K : RHKit) (T : Trace) : Prop := K.Proj (up T)
```

---

## The Triptych (T1 / T2 / T3)

### T1 — Rigidity

```lean
Rev0_K K T ↔ Halts T
```

Any valid kit collapses to standard halting. No hidden exotic power.

### T2 — Uniform Barrier

No internal predicate `H(e)` can be simultaneously total + correct + complete + r.e.

The barrier is the Π₁ side: "no witness will ever appear" requires stabilization, which cannot be uniformly internalized.

### T3 — Local Navigation

**OraclePick**: For each code `e`, a certificate selects either:
- `encode_halt e` (with `Rev0_K` witness)
- `encode_not_halt e` (with `KitStabilizes` witness)

**Extensions**: `S3 := S2 ∪ {pick.p}` preserves soundness.

**Quantifier Swap**:
- T2 forbids: `∃H ∀e` (uniform internal predicate)
- T3 permits: `∀e ∃Sₑ` (instancewise sound extension)

---

## OracleMachine Architecture

The non-mechanical power is localized:

- **a-machine** (mechanical): `Machine : Code → Trace`
- **c-machine** (compile): `compile : List Sentence → Sentence → Code`
- **o-bridge** (oracle): `SemConsequences Sat Γ φ ↔ Converges (compile Γ φ)`

Kits are not where the power is. Power lives in `Sat` / bridge / certificates.

---

## File Map

### Base Layer
- `RevHalt/Base/Trace.lean` — `Trace`, `Halts`, `up`
- `RevHalt/Base/Kit.lean` — `RHKit`, `DetectsMonotone`, `Rev0_K`

### Theory Layer
- `RevHalt/Theory/Canonicity.lean` — T1 (`T1_traces`, `T1_uniqueness`)
- `RevHalt/Theory/Impossibility.lean` — T2 (`diagonal_bridge`, `T2_impossibility`)
- `RevHalt/Theory/Complementarity.lean` — T3 (`OraclePick`, `S1Set`, `S3Set`)
- `RevHalt/Theory/Stabilization.lean` — `Stabilizes`, `KitStabilizes`, kernel link
- `RevHalt/Theory/Categorical.lean` — `up` as coreflector, `CloE`, `Frontier`, anti-monotonicity
- `RevHalt/Theory/QuantifierSwap.lean` — Quantifier Swap principle
- `RevHalt/Theory/ThreeBlocksArchitecture.lean` — OracleMachine, o-bridge, `ArchitecturalOraclePick`
- `RevHalt/Theory/Dynamics.lean` — Navigation dynamics: `State`, `step`, `Chain`, `lim`, soundness preservation
- `RevHalt/Theory/WitnessLogic.lean` — Witness soundness

---

## Build

```bash
lake build
```

---

## License / contribution

Add your license and contribution conventions here.
