import RevHalt.Base.Trace
import RevHalt.Base.Kit
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Categorical

/-!
# RevHalt.Theory.Stabilization

Turns the *negative* verdict of a valid Kit into a first-class Π₁ property.

- `Stabilizes T := ∀ n, ¬ T n` (Π₁)
  *Algebraically corresponding to `up T = ⊥` (see Theory/Categorical.lean).*
- `KitStabilizes K T := ¬ Rev0_K K T`
- `T1_stabilization`: if `DetectsMonotone K`, then `KitStabilizes K T ↔ Stabilizes T`
-/

namespace RevHalt

/-- Π₁ stabilization: the trace never becomes true. -/
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

theorem Stabilizes_iff_NotHalts (T : Trace) :
    Stabilizes T ↔ ¬ Halts T := by
  unfold Stabilizes Halts
  constructor
  · intro h hex
    rcases hex with ⟨n, hn⟩
    exact h n hn
  · intro h n hn
    exact h ⟨n, hn⟩

theorem Stabilizes_up_iff (T : Trace) :
    Stabilizes (up T) ↔ Stabilizes T := by
  rw [Stabilizes_iff_NotHalts, Stabilizes_iff_NotHalts]
  -- `Halts (up T) ↔ Halts T`
  have : Halts (up T) ↔ Halts T := (exists_up_iff T)
  tauto

/--
  **Bridge to Algebra**:
  Stabilization (logical) is equivalent to lying in the Kernel of `up` (algebraic).
-/
theorem Stabilizes_iff_up_eq_bot (T : Trace) :
  Stabilizes T ↔ up T = ⊥ := by
  exact (up_eq_bot_iff T).symm

/-- Kit-level negative verdict. -/
def KitStabilizes (K : RHKit) (T : Trace) : Prop := ¬ Rev0_K K T

theorem T1_stabilization (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T : Trace, KitStabilizes K T ↔ Stabilizes T := by
  intro T
  unfold KitStabilizes
  -- `Rev0_K K T ↔ Halts T`
  rw [T1_traces K hK T]
  -- `Stabilizes T ↔ ¬ Halts T`
  rw [Stabilizes_iff_NotHalts]

/--
  **The Kernel Detector Theorem**:
  A valid Kit detects exactly when a trace belongs to the kernel of `up`.
  `KitStabilizes K T ↔ up T = ⊥`

  This proves that the Kit is an instrument measuring the **algebraic nullity** of the trace.
-/
theorem KitStabilizes_iff_up_eq_bot (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    KitStabilizes K T ↔ up T = ⊥ := by
  rw [T1_stabilization K hK T]
  exact Stabilizes_iff_up_eq_bot T

end RevHalt
