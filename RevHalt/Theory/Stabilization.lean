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

/-- Constructive proof: Stabilizes (up T) ↔ Stabilizes T without Classical.choice -/
theorem Stabilizes_up_iff (T : Trace) :
    Stabilizes (up T) ↔ Stabilizes T := by
  rw [Stabilizes_iff_NotHalts, Stabilizes_iff_NotHalts]
  have h : Halts (up T) ↔ Halts T := (exists_up_iff T)
  constructor
  · intro hNotUp hT
    exact hNotUp (h.mpr hT)
  · intro hNotT hUp
    exact hNotT (h.mp hUp)

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

/--
  **Explicit Proof**:
  Same as `KitStabilizes_iff_up_eq_bot`, but with manual unfolding of the T1 layers.
  Shows step-by-step how `¬ Rev0` becomes `up T = ⊥`.
-/
theorem KitStabilizes_iff_up_eq_bot_explicit (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    (¬ Rev0_K K T) ↔ (up T = ⊥) := by
  -- ¬Rev ↔ ¬Halts (T1), puis ¬Halts ↔ ∀n ¬Tn, puis ↔ upT=⊥
  have h1 : Rev0_K K T ↔ Halts T := T1_traces K hK T
  -- transforme ¬Halts en ∀n ¬Tn
  -- et utilise up_eq_bot_iff
  constructor
  · intro hnot
    have : ¬ Halts T := by
      intro hH; exact hnot (h1.mpr hH)
    have hstab : ∀ n, ¬ T n := by
      intro n hn; exact this ⟨n, hn⟩
    exact (up_eq_bot_iff (T := T)).2 hstab
  · intro hupbot hrev
    have : Halts T := h1.mp hrev
    rcases this with ⟨n, hn⟩
    have : ∀ n, ¬ T n := (up_eq_bot_iff (T := T)).1 hupbot
    exact (this n) hn

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Stabilizes_iff_NotHalts
#print axioms RevHalt.Stabilizes_up_iff
#print axioms RevHalt.Stabilizes_iff_up_eq_bot
#print axioms RevHalt.T1_stabilization
#print axioms RevHalt.KitStabilizes_iff_up_eq_bot
#print axioms RevHalt.KitStabilizes_iff_up_eq_bot_explicit
