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
  The structural condition for a valid Kit: `DetectsUpFixed`.
  It states that for any *fixed point* of `up` (i.e. a closed/monotone trace),
  the Kit's projection agrees with standard existence.
-/
def DetectsUpFixed (K : RHKit) : Prop :=
  ∀ T : Trace, UpFixed T → (K.Proj T ↔ ∃ n, T n)

/--
  Abstract specification: `DetectsMono`.
  The Kit is correct on all monotone traces (pure monotonicity, no mention of `up`).
-/
def DetectsMono (K : RHKit) : Prop :=
  ∀ T : Trace, TMono T → (K.Proj T ↔ ∃ n, T n)

/-- Equivalence: DetectsMono ↔ DetectsUpFixed (via TMono ↔ UpFixed). -/
lemma DetectsMono_iff_DetectsUpFixed (K : RHKit) :
    DetectsMono K ↔ DetectsUpFixed K := by
  constructor
  · intro hM T hfix
    exact hM T (UpFixed_to_TMono T hfix)
  · intro hU T hmono
    exact hU T (TMono_to_UpFixed T hmono)

/--
  Rev_K: The Reverse Halting Operator.
  It standardizes the trace using `up` before applying the Kit.
-/
def Rev_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)

abbrev Rev0_K := Rev_K

/-- `Rev_K` agrees with standard halting on all traces, assuming `DetectsUpFixed`. -/
lemma revK_iff_halts (K : RHKit) (hK : DetectsUpFixed K) (T : Trace) :
    Rev_K K T ↔ Halts T := by
  -- unfold definitions
  unfold Rev_K Halts
  -- use DetectsUpFixed on the closed trace `up T`
  have hfix : UpFixed (up T) := up_fixed T
  -- K.Proj (up T) ↔ ∃ n, up T n
  have hdet : K.Proj (up T) ↔ ∃ n, up T n := hK (up T) hfix
  -- and ∃ n, up T n ↔ ∃ n, T n
  exact hdet.trans (exists_up_iff T)

/-- The “negative verdict” form: failure of `Rev_K` is equivalent to never halting. -/
lemma not_revK_iff_forall_not (K : RHKit) (hK : DetectsUpFixed K) (T : Trace) :
    ¬ Rev_K K T ↔ ∀ n, ¬ T n := by
  have h1 : Rev_K K T ↔ ∃ n, T n := by
    have h := revK_iff_halts K hK T
    unfold Halts at h
    exact h
  have h2 : ¬ Rev_K K T ↔ ¬ ∃ n, T n := not_congr h1
  -- Robust constructive proof for (¬ ∃ n, T n) ↔ ∀ n, ¬ T n
  have h3 : (¬ ∃ n, T n) ↔ ∀ n, ¬ T n := by
    constructor
    · intro h n hn
      exact h ⟨n, hn⟩
    · intro h hex
      obtain ⟨n, hn⟩ := hex
      exact (h n) hn
  exact h2.trans h3

/-- A convenient corollary: `Rev_K` is equivalent to `∃ n, up T n` (halts-by-up). -/
lemma revK_iff_exists_up (K : RHKit) (hK : DetectsUpFixed K) (T : Trace) :
    Rev_K K T ↔ ∃ n, up T n := by
  unfold Rev_K
  exact (hK (up T) (up_fixed T))

/-- Abstract version: `Rev_K` ↔ `Halts` using only `DetectsMono` (no mention of `UpFixed`). -/
lemma revK_iff_halts_of_DetectsMono (K : RHKit) (hK : DetectsMono K) (T : Trace) :
    Rev_K K T ↔ Halts T := by
  unfold Rev_K Halts
  -- up T is monotone (not UpFixed — pure TMono)
  have hmono : TMono (up T) := up_mono T
  -- apply kit correctness on monotone trace
  have hdet : K.Proj (up T) ↔ ∃ n, up T n := hK (up T) hmono
  exact hdet.trans (exists_up_iff T)

end RevHalt

-- Axiom checks:
#print axioms RevHalt.RHKit
#print axioms RevHalt.DetectsUpFixed
#print axioms RevHalt.DetectsMono
#print axioms RevHalt.DetectsMono_iff_DetectsUpFixed
#print axioms RevHalt.Rev_K
#print axioms RevHalt.revK_iff_halts
#print axioms RevHalt.revK_iff_halts_of_DetectsMono
#print axioms RevHalt.not_revK_iff_forall_not
#print axioms RevHalt.revK_iff_exists_up
