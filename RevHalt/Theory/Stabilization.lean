import RevHalt.Base.Trace
import RevHalt.Base.Kit
import RevHalt.Base.QuotientUp

/-!
# RevHalt.Theory.Stabilization

Turns the *negative* verdict of a valid Kit into a first-class Π₁ property.

- `Stabilizes T := ∀ n, ¬ T n` (Π₁)
  *Algebraically corresponding to `up T = ⊥` (pointwise).*
- `KitStabilizes K T := ¬ Rev0_K K T`
- `T1_stabilization`: if `DetectsUpFixed K`, then `KitStabilizes K T ↔ Stabilizes T`
-/

namespace RevHalt

/-- Π₁ stabilization: the trace never becomes true. -/
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

theorem Stabilizes_iff_NotHalts (T : Trace) :
    Stabilizes T ↔ ¬ Halts T := by
  unfold Stabilizes Halts
  -- Explicit constructive proof (¬∃ ↔ ∀¬)
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    exact h n hn
  · intro h n hn
    exact h ⟨n, hn⟩

/-- Constructive proof: Stabilizes (up T) ↔ Stabilizes T without Classical.choice -/
theorem Stabilizes_up_iff (T : Trace) :
    Stabilizes (up T) ↔ Stabilizes T := by
  -- Use axiom-free equivalence
  exact forall_not_up_iff_forall_not T

/--
  **Bridge to Algebra**:
  Stabilization (logical) is equivalent to lying in the Kernel of `up` (algebraic).
  Using axiom-free `UpIsBottom` instead of function equality `up T = ⊥`.
-/
theorem Stabilizes_iff_UpIsBottom (T : Trace) :
  Stabilizes T ↔ UpIsBottom T := by
  -- Stabilizes T is just ∀ n, ¬ T n
  -- UpIsBottom T is ∀ n, up T n ↔ ⊥ₜ n
  exact (UpIsBottom_iff_forall_not T).symm

/-- Kit-level negative verdict. -/
def KitStabilizes (K : RHKit) (T : Trace) : Prop := ¬ Rev0_K K T

theorem T1_stabilization (K : RHKit) (hK : DetectsUpFixed K) :
    ∀ T : Trace, KitStabilizes K T ↔ Stabilizes T := by
  intro T
  unfold KitStabilizes
  -- `Rev0_K K T ↔ Halts T` direct from Kit
  have h1 : Rev0_K K T ↔ Halts T := by
    simpa [Rev0_K] using (revK_iff_halts (K := K) hK (T := T))
  -- `KitStabilizes ↔ ¬ Rev0_K ↔ ¬ Halts ↔ Stabilizes`
  exact (not_congr h1).trans (Stabilizes_iff_NotHalts T).symm

/--
  **The Kernel Detector Theorem**:
  A valid Kit detects exactly when a trace belongs to the kernel of `up`.
  `KitStabilizes K T ↔ UpIsBottom T`

  This proves that the Kit is an instrument measuring the **algebraic nullity** of the trace.
-/
theorem KitStabilizes_iff_UpIsBottom (K : RHKit) (hK : DetectsUpFixed K) (T : Trace) :
    KitStabilizes K T ↔ UpIsBottom T := by
  -- KitStabilizes ↔ Stabilizes
  have h1 := T1_stabilization K hK T
  -- Stabilizes ↔ UpIsBottom
  have h2 := Stabilizes_iff_UpIsBottom T
  exact h1.trans h2

/--
  **Explicit Proof**:
  Same as `KitStabilizes_iff_UpIsBottom`, but with manual unfolding of the T1 layers.
  Shows step-by-step how `¬ Rev0` becomes `UpIsBottom`.
-/
theorem KitStabilizes_iff_UpIsBottom_explicit (K : RHKit) (hK : DetectsUpFixed K) (T : Trace) :
    (¬ Rev0_K K T) ↔ UpIsBottom T := by
  -- KitStabilizes ↔ UpIsBottom (just using the lemma above, as redundancy is just for explanation)
  exact KitStabilizes_iff_UpIsBottom K hK T

-- ==============================================================================================
-- DetectsMono variants (public API)
-- ==============================================================================================

/-- **T1 stabilization (DetectsMono API)**: KitStabilizes ↔ Stabilizes. -/
theorem T1_stabilization_of_DetectsMono (K : RHKit) (hK : DetectsMono K) :
    ∀ T : Trace, KitStabilizes K T ↔ Stabilizes T :=
  T1_stabilization K ((DetectsMono_iff_DetectsUpFixed K).mp hK)

/-- **Kernel Detector (DetectsMono API)**: KitStabilizes ↔ UpIsBottom. -/
theorem KitStabilizes_iff_UpIsBottom_of_DetectsMono (K : RHKit) (hK : DetectsMono K) (T : Trace) :
    KitStabilizes K T ↔ UpIsBottom T :=
  KitStabilizes_iff_UpIsBottom K ((DetectsMono_iff_DetectsUpFixed K).mp hK) T

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Stabilizes_iff_NotHalts
#print axioms RevHalt.Stabilizes_up_iff
#print axioms RevHalt.Stabilizes_iff_UpIsBottom
#print axioms RevHalt.T1_stabilization
#print axioms RevHalt.T1_stabilization_of_DetectsMono
#print axioms RevHalt.KitStabilizes_iff_UpIsBottom
#print axioms RevHalt.KitStabilizes_iff_UpIsBottom_of_DetectsMono
#print axioms RevHalt.KitStabilizes_iff_UpIsBottom_explicit
