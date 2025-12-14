# RevHalt

A Lean 4 framework proving that computational truth (halting) is:
- **Canonical** — independent of how you observe it
- **Inaccessible** — no sound formal system fully captures it
- **Complementary** — any sound theory can be strictly extended toward it

Unlike classical presentations of Gödel's theorems, which work *inside* a specific theory, RevHalt provides the abstract framework and treats theories (PA, ZFC) as instances to be plugged in.

---

## Architecture

The project follows a **Two-Level Architecture** to ensure compositionality and rigorous separation of concerns:

### 1. Abstract Level (Theory-Independent)
*Locations: `RevHalt.lean`, `RevHalt/Unified/Core.lean`*
- Formalizes the structural invariants of incompleteness (T2, T3) for **any** external truth predicate `RealHalts` inside a `TuringGodelContext`.
- At this level, theorems are logical validities independent of any specific theory or computation model.
- **Key Objects**: `RHKit`, `Trace`, `TuringGodelContext`.

### 2. Instantiated Level (The Bridge)
*Locations: `RevHalt/Unified/Bridge.lean`, `RevHalt/Unified/Coded/*.lean`, `RevHalt/Instances/*`*
- Connects the abstract world to concrete theories via the **M/L/A/E Interface**:
  - **M** (Model): A `RigorousModel` of computation (e.g., `PartrecCode`).
  - **L** (Logic): A `SoundLogicDef` (e.g., Peano Arithmetic).
  - **A** (Arithmetization): Maps definability in **M** to provability in **L**.
  - **E** (Encoding): Maps model halting to semantic truth.
- **Mechanism (Standard & Coded)**: The bridge instantiates `RealHalts` as `Rev0_K`. The `Coded` adapter handles theories (like PA) where only coded formula families are representable.
- **Result**: The abstract theorems (T1–T3) are automatically transported to the concrete theory without re-proof.

### How the Bridge Works

The goal is **compositionality**: once a theory provides an M/L/A/E instance, the entire T1 → T2 → T2' → T3 chain transports without rewriting proofs.

**Mechanism** (`Unified/Bridge.lean`):
1. **Instantiation**: Sets `RealHalts := Rev0_K K (rmCompile M e)` via `TGContext_from_RM`.
2. **Equivalence Chain**: Connects abstract halting to semantic truth using:
   - `T1_traces` (Rev0_K ↔ Halts)
   - `rm_compile_halts_equiv` (Halts ↔ RMHalts)
   - `encode_correct` (RMHalts ↔ Truth(HaltEncode))
3. **Transport**: `RevHalt_Master_Complete` delivers T1+T2+T2'+T3 for any valid instance.

This turns the framework into a **reference layer** for comparing theories in a common format.


### Original contributions

This project establishes three main results, each with distinct novelty:

#### T1 — Canonicity of computational truth

Classical result (Turing): *The halting problem is undecidable.*

T1 proves something different: **computational truth is objective** — independent of the observation mechanism.

The framework introduces `RHKit`, an abstract "observation mechanism" for traces. T1 proves:
- `T1_traces`: Any valid Kit yields the same verdict as standard halting
- `T1_uniqueness`: Two valid Kits are extensionally equivalent
- `T1_semantics`: Under the DynamicBridge hypothesis, Rev captures model-theoretic consequence

This is not Turing's theorem. It is a **canonicity result**: all valid observers converge to the same truth.

#### T2 — Abstract Turing-Gödel synthesis

Classical results: Turing (algorithmic undecidability) and Gödel I (true unprovable sentences) are typically presented separately.

T2 extracts their **common abstract core** via `TuringGodelContext'`:
- `diagonal_program`: the diagonal fixed-point axiom unifying both arguments
- Result: no internal predicate can be simultaneously Total, Correct, and Complete

This is not a reformulation; it is an **abstraction** that reveals the structural unity of Turing and Gödel.

#### The Oracle Perspective (New!)

We formalize the framework itself as a **Truth Oracle** (`RevHalt/Unified/Oracle.lean`).
- **Definition**: A `TruthOracle` is an external semantic authority that correctly judges propositions.
- **Theorem**: `oracle_not_internalizable`. A sound theory cannot "internalize" this oracle (i.e., simulate it via provability) without proving its own inconsistency (via T2).
- **Implication**: The bridge (`Truth ↔ Halts LR`) is not just a connector; it is an **essential oracular link** providing verdicts inaccessible to the theory's internal logic.

#### T3 — Complementarity: the central concept

Classical incompleteness is **limitative**: it tells you what theories *cannot* do.

T3 introduces a **new concept** — **complementarity** — and proves it formally:

> **Rev is the complement of any sound formal system.**

This means:
- Formal systems are not "failures" for being incomplete — they are **structurally partial**
- Rev is not merely "bigger" than PA/ZFC — it is **what they lack**
- Truth and provability are not opposed — they are **complementary**

The theorem `T3_strong` proves that this complementarity is **structured and rich**, given an `InfiniteIndependentHalting` hypothesis (an infinite family of independent halting codes). Under this assumption, we prove the existence of **infinitely many disjoint, compatible directions** of extension. This means that completing a theory is not a single forced step, but a **dynamical choice** — a navigation through the geography of computational truth.

**This concept has no classical analog.** It transforms incompleteness from a limitative statement into a structural dynamical relationship.

---

## Syntax–semantics correspondence

The framework establishes a precise correspondence:

| RevHalt (syntax) | Instance L (semantics) |
|------------------|------------------------|
| `RMHalts e` — halting defined by the computability model | `L.Truth (HaltEncode e)` — truth as seen by the theory |
| `M.PredDef` — definability in the abstract model | `L.Provable` via arithmetization — derivability as seen by the theory |
| Diagonalization (`diagonal_halting`) | Arithmetization (`repr_provable_not`) |

The theorems then express structural gaps between syntactic truth and semantic observability:

| Theorem | Interpretation |
|---------|----------------|
| **T1** : `∀ T, Rev0_K K T ↔ Halts T` | **Canonicity**: computational truth is objective, independent of observation mechanism |
| **T2** : `∃ p, Truth p ∧ ¬Provable p` | **Synthesis**: no internal predicate captures external truth (Turing-Gödel core) |
| **T2'** : `∃ e, ¬Provable(H e) ∧ ¬Provable(¬H e)` | **Independence**: some halting facts are invisible to the semantic observer |
| **T3** : `∃ T₁ ⊃ ProvableSet, sound` | **Complementarity**: Rev provides structured infinite extensions for any sound theory |

This is the reverse of classical incompleteness proofs, which work *in* a theory *about* that theory. Here, the proofs work *in* RevHalt *about* any conforming semantic instance.

---

## Structure

### Core modules

| Module | Contents |
|--------|----------|
| `RevHalt.lean` | Base layer: `Trace`, `Halts`, `RHKit`, `TuringGodelContext'`, `T2_impossibility` |
| `RevHalt.Unified.Core` | Abstract results: `EnrichedContext`, `ProvableSet`, `true_but_unprovable_exists`, `independent_code_exists` |
| `RevHalt.Unified.Oracle` | Meta-theory: `TruthOracle`, `InternalizesOracle`, `oracle_not_internalizable`, `bridge_is_oracular` |
| `RevHalt.Unified.RigorousModel` | Computability model: `RigorousModel`, `SoundLogicDef`, `Arithmetization` |
| `RevHalt.Unified.Bridge` | Integration: `SoundLogicEncoded`, `EnrichedContext_from_Encoded`, `RevHalt_Master_Complete` |

### Entry point

```lean
import RevHalt.Unified
open RevHalt_Unified
```

---

## Interface (M / L / A / E)

The framework factors assumptions into four components:

### M — Computability model (`RigorousModel`)

- `Code`, `Program : Code → ℕ → Option ℕ`
- `PredCode`, `PredDef : PredCode → Code → Prop` (definability, not decidability)
- `diagonal_halting` (fixed-point over definable predicates)
- `no_complement_halts` (non-halting is not definable)

### L — Logic (`SoundLogicDef PropT`)

- `Provable`, `Truth : PropT → Prop`
- `soundness : Provable p → Truth p`
- `Not`, `FalseP`, `consistent`, `absurd`, `truth_not_iff`

### A — Arithmetization (`Arithmetization M PropT L`)

- `repr_provable_not` : for any `G : Code → PropT`, the predicate `Provable (Not (G e))` is definable in `PredCode`.

### E — Encoding (in `SoundLogicEncoded`)

- `HaltEncode : Code → PropT`
- `encode_correct : RMHalts e ↔ Truth (HaltEncode e)`

---

## Main theorem

### `RevHalt_Master_Complete`

For any semantic instance `(M, K, L)` satisfying the interface:

```
(1) ∀ e, RealHalts e ↔ Halts (compile e)           -- T1: canonicity
(2) ∃ p, Truth p ∧ ¬Provable p                     -- T2: synthesis
(3) ∃ e, ¬Provable (H e) ∧ ¬Provable (Not (H e))   -- T2': independence
(4) ∃ T₁ ⊃ ProvableSet, ∀ p ∈ T₁, Truth p         -- T3: complementarity
```

---

## Demos

- `RevHalt_Demo_A` : trivial model (empty provability)
- `RevHalt_Demo_C` : non-trivial model (non-empty provability, structured predicates)
- `RevHalt/Demo/Template.lean` : instantiation skeleton

---

## Build

```bash
lake build
lake env lean RevHalt/Demo/All.lean
```

---

## Design notes

- `PredDef` is `Prop`-valued (definability), avoiding implicit decidability assumptions.
- `no_complement_halts` blocks trivial instantiations where "not halts" would be definable.
- Soundness (`Provable → Truth`) is an explicit hypothesis, not an ambient assumption.

---

## LLM Disclosure

The code and documentation in this repository were primarily generated by Large Language Models (specifically ChatGPT) under the strict conceptual guidance of the author.

**Methodology:**
- **Conceptual Design**: The core definitions, architectural constraints, and theorem statements were specified by the author.
- **Implementation**: The expansion of these concepts into valid Lean 4 code was performed by the LLM through an iterative process of generation, compilation, error analysis, and refinement.
- **Verification**: The final authority is the Lean 4 kernel. The role of the LLM was to produce a formal text that satisfies the compiler's strict consistency checks.

This project demonstrates how agentic AI can be used to translate private conceptual frameworks into rigorous, machine-checked mathematical artifacts.

