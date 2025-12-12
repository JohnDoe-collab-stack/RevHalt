# RevHalt Unified

RevHalt is a modular Lean framework that derives incompleteness-style results from a computation-first foundation (Turing-style halting + diagonalization), without taking the "proof strength" of any particular theory (ZFC, PA, etc.) as the starting point.

The key point: ZFC/PA-like systems appear as *local instances* inside a broader calculational semantics. Their provability predicates become *local syntactic observers* of an externally defined notion of truth.

---

## What this project claims (informally)

For any formal theory you plug into the framework (via minimal, explicit hypotheses), the framework constructs a context in which:

- there exists a statement that is true but not provable in the theory,
- there exists a halting statement that the theory cannot decide on either side,
- and the set of provable truths can always be strictly extended while preserving soundness.

These are not "about ZFC in particular". They are uniform consequences of the M/L/A/E interface described below.

---

## Module structure

- `RevHalt.Unified.Core`
  - Abstract T1/T2/T3 logic:
    - `TuringGodelContext'`, `EnrichedContext`
    - `true_but_unprovable_exists`, `independent_code_exists`
    - `ProvableSet` and sound extension lemmas

- `RevHalt.Unified.RigorousModel`
  - Computability foundation and representability boundary:
    - `RigorousModel` (partial semantics, definability via `PredDef : PredCode → Code → Prop`)
    - `RMHalts`, `rmCompile`, `rm_compile_halts_equiv`
    - `SoundLogicDef` (pure logic, theory-local)
    - `Arithmetization` (representability of provability under definability)

- `RevHalt.Unified.Bridge`
  - Integration layer:
    - `SoundLogicEncoded` (bundles Logic + Arithmetization + a halting encoding)
    - `EnrichedContext_from_Encoded`
    - `RevHalt_Master_Complete` (the main theorem: T1 + T2 + T2' + T3)

Public entry point:

- `RevHalt/Unified.lean`
  - Imports `Core`, `RigorousModel`, `Bridge` as a single API.

---

## Hypotheses (M / L / A / E)

The framework separates assumptions into four components:

### M — Computability model (`RigorousModel`)
You provide:
- `Code` and `Program : Code → Nat → Option Nat`
- `PredCode` and `PredDef : PredCode → Code → Prop` (definability, not decidability)
- `diagonal_halting` (diagonalization over definable predicates)
- `no_complement_halts` (coherence: "not halts" is not definable in `PredCode`)
- a non-halting code

### L — Pure logic (`SoundLogicDef PropT`)
You provide, for your proposition type `PropT`:
- `Provable : PropT → Prop` (syntactic derivability in your theory)
- `Truth : PropT → Prop` (your chosen semantics / meta-truth for that theory)
- `soundness : Provable p → Truth p` (explicit soundness hypothesis)
- `Not`, `FalseP`, plus consistency/absurdity and classical negation for `Truth`

### A — Arithmetization (`Arithmetization M PropT L`)
You provide the representability bridge:
- for any `G : Code → PropT`, the predicate "Provable (Not (G e))" is definable via some `PredCode`.

Intuition: the meta-level computability model can express the theory's provability behavior in the definability system.

### E — Halting encoding (inside `SoundLogicEncoded`)
You provide:
- `HaltEncode : Code → PropT` (a proposition representing "e halts")
- `encode_correct : RMHalts e ↔ Truth (HaltEncode e)` (semantic correctness)

---

## Main result

### `RevHalt_Master_Complete`

Given `M`, a kit `K` satisfying T1's monotone detection, and `SoundLogicEncoded` (L + A + E), the theorem yields:

1. RealHalts matches concrete execution (T1 alignment)
2. Existence of a true-but-unprovable proposition (T2)
3. Existence of an independent halting instance:
   - not provable that it halts
   - not provable that it does not halt
4. Strict sound extension:
   - the set of provable propositions can be strictly enlarged while staying within truth

---

## Why this is "foundational" in the intended sense

This framework does not treat "ZFC strength" or "PA strength" as a base primitive.

Instead, it takes computation (halting + diagonalization) as the base layer, then treats any formal theory as an *instance* obtained by supplying:

- its internal provability predicate (syntax),
- a chosen truth semantics (meta),
- and explicit bridges showing that the theory can be arithmetized and can express halting.

In that sense, "proof strength" becomes a local property of an observer: it describes which portion of the externally grounded computability truth the theory can capture.

---

## Usage

### Import everything (public API)

```lean
import RevHalt.Unified
open RevHalt_Unified
```

### Instantiate via the template

See `RevHalt/Demo/Template.lean` for a minimal copy/paste instantiation skeleton:

* define/axiomatize your `Program`, `PredDef`, `Provable`, `Truth`, `Not`, `FalseP`
* prove/axiomatize diagonal + coherence + soundness + arithmetization + halting encoding
* bundle into `SoundLogicEncoded`
* apply `RevHalt_Master_Complete`

---

## Demo suite

* `RevHalt_Demo_A`:
  * simple model, empty provability

* `RevHalt_Demo_C`:
  * non-empty provability, non-trivial predicates, non-trivial truth

Test entry point:

* `RevHalt/Demo/All.lean` imports demos and contains smoke tests.

---

## Build / run

Typical commands:

```bash
lake build
lake env lean RevHalt/Demo/All.lean
```

A successful compilation validates:

* module boundaries,
* the Bridge integration,
* and the demo instantiations of the Master theorem.

---

## Design notes

* `PredDef` is Prop-valued (definability), avoiding hidden decidability assumptions.
* `no_complement_halts` is the explicit coherence boundary that blocks trivializing the framework by definably representing "not halts".
* Soundness is always explicit: "Truth" is provided as a semantics, not assumed by default.
