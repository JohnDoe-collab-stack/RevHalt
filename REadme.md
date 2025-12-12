# RevHalt

A Lean 4 framework proving that computational truth (halting) is:
- **Canonical** — independent of how you observe it
- **Inaccessible** — no sound formal system fully captures it
- **Complementary** — any sound theory can be strictly extended toward it

Unlike classical presentations of Gödel's theorems, which work *inside* a specific theory, RevHalt provides the abstract framework and treats theories (PA, ZFC) as instances to be plugged in.

---

## Foundational perspective

Standard presentations of Gödel's incompleteness theorems work *within* a base theory (typically PA or ZFC) and derive limitative results about that theory's expressive power.

This project inverts the perspective:

- **RevHalt provides the abstract syntactic framework**, grounded in Turing-style computability (halting, diagonalization, definability).
- **Formal theories become semantic instances** of this framework, obtained by supplying concrete interpretations of the abstract interface (provability, truth, arithmetization).

In this formulation, the "proof strength" of any particular theory is not a primitive notion but rather emerges as a local property: it measures how much of the externally-defined computational truth the theory's provability predicate can capture.

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

#### T3 — Complementarity: the central concept

Classical incompleteness is **limitative**: it tells you what theories *cannot* do.

T3 introduces a **new concept** — **complementarity** — and proves it formally:

> **Rev is the complement of any sound formal system.**

This means:
- Formal systems are not "failures" for being incomplete — they are **structurally partial**
- Rev is not merely "bigger" than PA/ZFC — it is **what they lack**
- Truth and provability are not opposed — they are **complementary**

The theorem `T3_strong` proves that this complementarity is **structured and rich**. The space of true-but-unprovable statements is not an amorphous limiting void, but a **partitioned landscape**.

We prove the existence of **infinitely many disjoint, compatible directions** of extension. This means that completing a theory is not a single forced step, but a **dynamical choice** — a navigation through the geography of computational truth.

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
