-- RevHalt/Checks/Lint.lean
-- One-file validation: imports all demos + runs linter

import RevHalt.Demo.All

/-!
# RevHalt Lint Check

Run this file to validate the entire project:

```bash
lake env lean RevHalt/Checks/Lint.lean
```

A successful compilation (Exit 0) means:
1. All demos compile
2. All smoke tests pass
3. No linter errors (if #lint is uncommented)
-/

-- Uncomment to run linter (requires Mathlib.Tactic.Lint):
-- import Mathlib.Tactic.Lint
-- #lint
