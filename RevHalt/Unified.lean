-- RevHalt/Unified.lean
-- Single entry point (public API)

import RevHalt.Unified.Exports

/-!
# RevHalt Unified (Public API)

Importer ce fichier suffit pour tout usage externe.

## Usage

```lean
import RevHalt.Unified
open RevHalt_Unified

#check RigorousModel
#check SoundLogicEncoded
#check RevHalt_Master_Complete
```

## Public API (from Exports.lean)

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

## Module Structure

- `RevHalt.Unified.Exports` — Explicit API surface
- `RevHalt.Unified.Core` — Abstract T1-T2-T3 logic
- `RevHalt.Unified.RigorousModel` — Computability model
- `RevHalt.Unified.Bridge` — SoundLogicEncoded + Master Theorem

## Validation

```bash
lake build
lake env lean RevHalt/Demo/All.lean
lake env lean RevHalt/Checks/Lint.lean
```
-/
