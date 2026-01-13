import RevHalt.Base.Trace

/-!
# RevHalt.Base.Kit

Reverse Halting Kit structure and DetectsMonotone property.

## Contents
- `RHKit` structure
- `DetectsMonotone` predicate
- `Rev_K`, `Rev0_K` operators
-/

namespace RevHalt

/-- Reverse Halting Kit structure. Represents an abstract observation mechanism. -/
structure RHKit where
  Proj : Trace → Prop

/--
  The structural condition for a valid Kit: `DetectsMonotone`.
  It states that for any *monotone* process, the Kit's projection agrees with standard existence.
  This allows the Kit to have "exotic" behavior on non-monotone traces, but it must be standard on monotone ones.
-/
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ ∃ n, X n)

/--
  Rev_K: The Reverse Halting Operator.
  It standardizes the trace using `up` before applying the Kit.
-/
def Rev_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)

abbrev Rev0_K := Rev_K

/-- `Rev_K` agrees with standard halting on all traces, assuming `DetectsMonotone`. -/
lemma revK_iff_halts (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    Rev_K K T ↔ Halts T := by
  -- unfold definitions
  unfold Rev_K Halts
  -- use DetectsMonotone on the monotone trace `up T`
  have hmono : Monotone (up T) := up_mono T
  -- K.Proj (up T) ↔ ∃ n, up T n
  have hdet : K.Proj (up T) ↔ ∃ n, up T n := hK (up T) hmono
  -- and ∃ n, up T n ↔ ∃ n, T n
  exact hdet.trans (exists_up_iff T)

/-- The “negative verdict” form: failure of `Rev_K` is equivalent to never halting. -/
lemma not_revK_iff_forall_not (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    ¬ Rev_K K T ↔ ∀ n, ¬ T n := by
  -- rewrite `Rev_K` into `Halts` using the previous lemma
  have : Rev_K K T ↔ Halts T := revK_iff_halts (K := K) hK (T := T)
  -- unfold Halts and use classical/constructive logic: ¬∃ ↔ ∀¬ (constructive)
  unfold Halts at this
  -- now `this` is: Rev_K K T ↔ ∃ n, T n
  -- so negating both sides yields the desired statement
  -- Lean has `not_exists` simp lemma: ¬ (∃ n, T n) ↔ ∀ n, ¬ T n
  simp [this]

/-- A convenient corollary: `Rev_K` is equivalent to `∃ n, up T n` (halts-by-up). -/
lemma revK_iff_exists_up (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    Rev_K K T ↔ ∃ n, up T n := by
  unfold Rev_K
  exact (hK (up T) (up_mono T))

end RevHalt

-- Axiom checks:
#print axioms RevHalt.RHKit
#print axioms RevHalt.DetectsMonotone
#print axioms RevHalt.Rev_K
#print axioms RevHalt.revK_iff_halts
#print axioms RevHalt.not_revK_iff_forall_not
#print axioms RevHalt.revK_iff_exists_up
