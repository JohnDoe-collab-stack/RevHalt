-- RevHalt/Demo/All.lean
-- Entry point for the full Demo test suite

import RevHalt.Demo.DemoA
import RevHalt.Demo.DemoC
import RevHalt.Demo.SimpDemo

/-!
# RevHalt Demo Suite

This file imports all demo models for testing and validation.

## Models

- `DemoA`: Degenerate model (empty provability)
- `DemoC`: Robustness model (non-empty provability, non-trivial predicates)

## Usage

```bash
lake env lean RevHalt/Demo/All.lean
```

A successful compilation (Exit 0) validates the entire framework.
-/

-- ==============================================================================================
-- Smoke Tests
-- ==============================================================================================

section SmokeTests

open RevHalt_Unified

-- Core structures
#check RigorousModel
#check SoundLogicDef
#check Arithmetization
#check SoundLogicEncoded
#check EnrichedContext

-- Key functions
#check TGContext_from_RM
#check EnrichedContext_from_Encoded

-- Master theorem
#check RevHalt_Master_Complete

-- Demo theorems
#check RevHalt_Demo_A.Toy_Master_Theorem
#check RevHalt_Demo_C.Toy_C_Master_Theorem

end SmokeTests
