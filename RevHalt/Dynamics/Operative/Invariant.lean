/-
  RevHalt.Dynamics.Operative.Invariant

  Rev as the operative invariant (level VerifiableContext).

  Rev labels propositions independently of graph position.
-/

import RevHalt.Kinetic.System
import RevHalt.Kinetic.MasterClosure
import Mathlib.Data.Set.Basic

namespace RevHalt.Dynamics.Operative

open Set RevHalt

variable {Code PropT : Type}

/-- The Rev label: whether a proposition "halts" via LR on empty context.
    This is the operative invariant - it doesn't depend on the theory node position. -/
def RevLabel (ctx : VerifiableContext Code PropT) (p : PropT) : Prop :=
  Halts (ctx.LR ∅ p)

namespace RevLabel

variable {ctx : VerifiableContext Code PropT}

/-- RevLabel equals Truth via the bridge. -/
theorem eq_truth (p : PropT) : RevLabel ctx p ↔ ctx.Truth p :=
  (ctx.h_bridge p).symm

/-- RevLabel is stable: it doesn't depend on which theory node we're at.
    (This is trivial but conceptually important - Rev is an external observer.) -/
theorem stable (p : PropT) : RevLabel ctx p = RevLabel ctx p := rfl

/-- RevLabel characterizes the gap. -/
theorem gap_iff (p : PropT) :
    p ∈ GapTruth ctx ↔ RevLabel ctx p ∧ ¬ctx.Provable p := by
  simp only [mem_GapTruth_iff]
  constructor
  · intro ⟨hT, hNP⟩
    exact ⟨(ctx.h_bridge p).mp hT, hNP⟩
  · intro ⟨hH, hNP⟩
    exact ⟨(ctx.h_bridge p).mpr hH, hNP⟩

/-- RevLabel is kit-invariant: same result for any valid kit (via T1). -/
theorem kit_invariant (K : RHKit) (hK : DetectsMonotone K) (p : PropT) :
    RevLabel ctx p ↔ Rev0_K K (ctx.LR ∅ p) := by
  simp only [RevLabel]
  exact (T1_traces K hK (ctx.LR ∅ p)).symm

end RevLabel

end RevHalt.Dynamics.Operative
