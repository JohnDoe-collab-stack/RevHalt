# RevHalt Extensions

This directory contains **experimental and future work** extensions to the core RevHalt framework.

## Status: Extensions (Non-Core)

The modules in this directory are **not part of the main RevHalt theorems** (T1/T2/T3, Master_Closure, TheGreatChain).
They provide infrastructure for potential future work.

---

## Contents

### `RefSystem.lean`
**Status**: ⚠️ Placeholder / Toy Implementation

Defines a framework for encoding referents via:
- `Cut` : Rational approximations
- `Bit` : Binary digit encodings
- `LR_ref` : Local reading (currently a "toy condition")

**Use Case**: Intended for computability of real numbers (e.g., Chaitin's Ω).

**Integration**: Defines `DR0_ref` and `DR1_ref` theorems connecting to `Closure.lean`, but these are currently unused by the main project.

---

### `OmegaChaitin.lean`
**Status**: ⚠️ Axiomatized Skeleton

Provides a conceptual instance of `RefSystem` for Chaitin's halting probability Ω.

**Contents**:
- `OmegaApprox : ℕ → ℚ` (axiomatized)
- `OmegaSentence` : Sentences about Ω
- `LR_omega` : Local reading for Ω verification
- `TheGreatChain` specialization for Ω

**Limitations**:
- `OmegaApprox` is axiomatized (not constructively defined)
- No real integration with the main theorem chain
- Intended as a proof-of-concept for extending RevHalt to continuous domains

---

## Future Work

To make these extensions production-ready:

1. **RefSystem**: Implement a concrete `LR_ref` that meaningfully tests progressive bit/cut refinement
2. **OmegaChaitin**: Define `OmegaApprox` constructively via program enumeration using `Nat.Partrec.Code`
3. **Integration**: Create a concrete theorem showing how Ω's undecidability maps to the `Gap` characterization in `System.lean`

---

## Usage

These files are **not imported by the core modules**. To experiment with them:

```lean
import RevHalt.Extensions.RefSystem
import RevHalt.Extensions.OmegaChaitin
```

For production work, use only the `RevHalt.Unified.*` modules.
