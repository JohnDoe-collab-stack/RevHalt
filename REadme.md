# RevHalt

A Lean 4 formalization of incompleteness and undecidability results, where the framework itself serves as the syntactic foundation and formal theories (PA, ZFC, etc.) appear as semantic instances.

---

## Foundational perspective

Standard presentations of Gödel's incompleteness theorems work *within* a base theory (typically PA or ZFC) and derive limitative results about that theory's expressive power.

This project inverts the perspective:

- **RevHalt provides the abstract syntactic framework**, grounded in Turing-style computability (halting, diagonalization, definability).
- **Formal theories become semantic instances** of this framework, obtained by supplying concrete interpretations of the abstract interface (provability, truth, arithmetization).

In this formulation, the "proof strength" of any particular theory is not a primitive notion but rather emerges as a local property: it measures how much of the externally-defined computational truth the theory's provability predicate can capture.

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
(1) ∀ e, RealHalts e ↔ Halts (compile e)           -- T1: alignment
(2) ∃ p, Truth p ∧ ¬Provable p                     -- T2: incompleteness
(3) ∃ e, ¬Provable (H e) ∧ ¬Provable (Not (H e))   -- T2': independence
(4) ∃ T₁ ⊃ ProvableSet, ∀ p ∈ T₁, Truth p         -- T3: strict extension
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
