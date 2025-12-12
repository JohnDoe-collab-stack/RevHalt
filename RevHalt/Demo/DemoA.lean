-- RevHalt/Demo/DemoA.lean
-- Re-exports RevHalt_Demo_A for the Demo test suite

import RevHalt_Demo_A

/-!
# Demo A: Degenerate Model

A minimal model demonstrating the framework:
- `toyProgram`: Code 0 halts, all others loop
- `toyProvable := False` (empty provability)
- `toyTruth p := p = 0`

This validates the basic theorem structure.
-/
