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
  Proj : (ℕ → Prop) → Prop

/--
  The core axiom for a valid Kit: `DetectsMonotone`.
  It states that for any *monotone* process, the Kit's projection agrees with standard existence.
  This allows the Kit to have "exotic" behavior on non-monotone traces, but it must be standard on monotone ones.
-/
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : ℕ → Prop, Monotone X → (K.Proj X ↔ ∃ n, X n)

/--
  Rev_K: The Reverse Halting Operator.
  It standardizes the trace using `up` before applying the Kit.
-/
def Rev_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)

abbrev Rev0_K := Rev_K

end RevHalt
