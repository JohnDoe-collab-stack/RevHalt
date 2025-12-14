-- Base Layer: Trace, Halts, RHKit
import RevHalt.Base

-- Theory Layer: T1/T2/T3 abstract theorems
import RevHalt.Theory

-- Bridge Layer: M/L/A/E instantiation
import RevHalt.Bridge

-- Kinetic Layer: Dynamic semantics
import RevHalt.Kinetic

-- Oracle Layer: Framework as oracle
import RevHalt.Oracle

-- Extensions: RefSystem, OmegaChaitin
import RevHalt.Extensions

-- Instances: PRModel, PA
import RevHalt.Instances

/-!
# RevHalt

Public API entry point for the RevHalt framework.

## Quick Start

```lean
import RevHalt
open RevHalt
```

## Main Exports

### Structures
- `Trace`, `Halts` — Basic trace definitions
- `RHKit`, `DetectsMonotone` — Observation mechanism
- `TuringGodelContext'` — Abstract Turing-Gödel context
- `RigorousModel` — Computability model
- `SoundLogicDef` — Pure logic interface
- `SoundLogicEncoded` — Full M/L/A/E package
- `EnrichedContext` — Context with Truth for T2/T3

### Theorems
- `T1_traces` — Canonicity: Rev0_K = Halts
- `T2_impossibility` — No total+correct+complete internal predicate
- `T3_strong` — Disjoint families of sound extensions
- `RevHalt_Master_Complete` — T1 + T2 + T2' + T3

### Kinetic Layer
- `CloK`, `CloRev` — Kinetic closures
- `VerifiableContext`, `GapSystem` — Gap reasoning
- `Chain`, `MasterClo`, `GapLayer` — Stratified dynamic gaps
- `Truth_for_all_of_MasterClo_univ` — Local→global reduction

### Oracle Perspective
- `TruthOracle`, `oracle_not_internalizable`

## Validation

```bash
lake build
```
-/

-- Re-export main namespace
-- All symbols from imported modules are already accessible via `open RevHalt`
