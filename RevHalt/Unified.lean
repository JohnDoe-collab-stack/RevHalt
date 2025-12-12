-- RevHalt/Unified.lean
-- Single entry point for RevHalt.Unified modules

import RevHalt.Unified.Core
import RevHalt.Unified.RigorousModel
import RevHalt.Unified.Bridge

/-!
# RevHalt Unified (Public API)

This file is the single entry point for the modularized RevHalt architecture.
Import only this file for access to the complete framework.

## Public API (Exports)

### Structures
- `RigorousModel` — Foundational computability model
- `SoundLogicDef` — Pure logic (no model dependency)
- `Arithmetization` — Gödelian representability bridge
- `SoundLogicEncoded` — Full package (Logic + Arith + HaltEncode)
- `EnrichedContext` — Context with Truth for T2/T3 proofs

### Constructions
- `TGContext_from_RM` — Build `TuringGodelContext'` from M/K/L/A
- `EnrichedContext_from_Encoded` — Build full context for Master Theorem

### Theorems
- `RevHalt_Master_Complete` — T1 + T2 + T2' + T3 (main result)
- `RevHalt_Master_Rigorous` — Diagonal existence (intermediate)

### Utilities
- `RMHalts`, `rmCompile`, `rm_compile_halts_equiv` — Halting semantics
- `ProvableSet`, `true_but_unprovable_exists`, `independent_code_exists` — Core results

## Usage

```lean
import RevHalt.Unified
open RevHalt_Unified

-- Access all public definitions
#check RigorousModel
#check SoundLogicEncoded
#check RevHalt_Master_Complete
```

## Module Structure

- `RevHalt.Unified.Core` — Abstract T1-T2-T3 logic
- `RevHalt.Unified.RigorousModel` — Computability model + SoundLogicDef + Arithmetization
- `RevHalt.Unified.Bridge` — SoundLogicEncoded + Master Theorem

## Namespace

All definitions are in namespace `RevHalt_Unified`.
-/

-- Re-export the namespace for convenience
namespace RevHalt_Unified
-- All exports are available via the imports above
end RevHalt_Unified
