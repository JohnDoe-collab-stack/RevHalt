-- RevHalt/Demo/DemoC.lean
-- Re-exports RevHalt_Demo_C for the Demo test suite

import RevHalt_Demo_C

/-!
# Demo C: Robustness Model

A more sophisticated model testing the framework robustness:
- `toyProgram`: Code 0 halts, all others loop
- `toyProvable p := p = 0` (non-empty provability)
- `toyTruth p := p % 2 = 0` (evenness)
- `toyPredDef`: Non-trivial cases (False, True, Halting)

This validates that the theorems hold even with non-empty provability.
-/
