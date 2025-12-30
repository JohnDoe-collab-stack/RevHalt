import RevHalt.Base.Trace
import RevHalt.Base.Kit
import RevHalt.Theory.Canonicity

/-!
# RevHalt.Theory.Stabilization

**P1 Access via Kit.**

This file formalizes "Stabilization" as a first-class property derived directly
from the Kit's negative verdict (via T1).

## Definitions

- `Stabilizes T`: The trace never becomes true (∀ n, ¬ T n). This is strictly Π₁.
- `KitStabilizes K T`: The Kit output is false (`¬ Rev0_K K T`).
- `T1_stabilization`: The bridge theorem. If K detects monotone, then `KitStabilizes ↔ Stabilizes`.
-/

namespace RevHalt

-- ==============================================================================================
-- 1. The Trace Level: P1 Definition
-- ==============================================================================================

/--
  **Stabilizes**: A trace stabilizes (to false) if it never becomes true.
  Structure: `∀ n, ¬ T n` (Π₁).
  This is the constructive negation of `Halts`.
-/
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

/--
  Equivalence: Stabilization corresponds exactly to Non-Halting.
  `Stabilizes T ↔ ¬ (∃ n, T n)`
-/
theorem Stabilizes_iff_NotHalts (T : Trace) :
    Stabilizes T ↔ ¬ Halts T := by
  unfold Stabilizes Halts
  push_neg
  rfl

/--
  **Stability under Closure**:
  The `up` operator preserves stabilization exactly.
  If the original trace never fires, the closure never fires.
-/
theorem Stabilizes_up_iff (T : Trace) :
    Stabilizes (up T) ↔ Stabilizes T := by
  rw [Stabilizes_iff_NotHalts, Stabilizes_iff_NotHalts]
  unfold Halts
  rw [exists_up_iff T]

-- ==============================================================================================
-- 2. The Kit Level: P1 Certificate
-- ==============================================================================================

/--
  **KitStabilizes**: The Kit's formal verdict for "No".
  This is an observational property: "The instrument output is false".
-/
def KitStabilizes (K : RHKit) (T : Trace) : Prop :=
  ¬ Rev0_K K T

/--
  **Theorem T1 (Stabilization)**:
  If the Kit is valid (DetectsMonotone), then a negative verdict
  is a **Proof of Stabilization**.

  This gives us Π₁ access "on a budget": we don't compute the infinite check,
  we observe the Kit's rejection.
-/
theorem T1_stabilization (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T : Trace, KitStabilizes K T ↔ Stabilizes T := by
  intro T
  unfold KitStabilizes
  -- Use T1: Rev0_K K T ↔ Halts T
  rw [T1_traces K hK T]
  -- Use Stabilizes ↔ ¬ Halts
  rw [← Stabilizes_iff_NotHalts]

end RevHalt
