import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.Impossibility
import RevHalt.Base.Kit  -- Need for DetectsMono, Halts, etc.

namespace RevHalt

open Set

/-!
# Invariance of Stability under Reductions

We show that the "Stability" condition (`S1Rel = ∅`) is robust: it is preserved
under computable reductions that are provable in the theory.

This justifies focusing on TSP (or 3-SAT) as a representative instance: if one
NP-complete problem has an empty frontier, they all do (under moderate assumptions).

## Main Definitions

* `ReducibleSystem`: A reduction from `(M1, Code1)` to `(M2, Code2)` consisting of:
  - A computable function `f : Code1 → Code2`
  - A proof that `Halts(M1 p) ↔ Halts(M2 (f p))`
  - A proof that `Provable S (encode_halt1 p) ↔ Provable S (encode_halt2 (f p))`

* `Invariance`: `S1Rel_empty (M2) → S1Rel_empty (M1)`

-/

section Invariance

variable {PropT : Type} -- [PartialOrder PropT] removed as unused
variable {Code1 Code2 : Type}
variable (M1 : Code1 → Trace) (M2 : Code2 → Trace) -- Trace is the output of Machine
variable (K : RHKit)
variable (Provable : Set PropT → PropT → Prop)
variable (ωΓ : Set PropT)
variable (encode_halt1 : Code1 → PropT)
variable (encode_halt2 : Code2 → PropT)

/--
A reduction from System 1 (M1) to System 2 (M2).
We require that the reduction `f` preserves halting status and that this preservation
is "known" (or at least respects) the provability relation.
-/
structure ReducibleSystem where
  toCode : Code1 → Code2
  -- Halting is preserved (semantic truth)
  halts_iff : ∀ p, RevHalt.Halts (M1 p) ↔ RevHalt.Halts (M2 (toCode p))
  -- Provability is preserved (semantic provability)
  provable_iff : ∀ p, Provable ωΓ (encode_halt1 p) ↔ Provable ωΓ (encode_halt2 (toCode p))

/--
Theorem: If System 1 reduces to System 2, and System 2 is stable (no unprovable truths),
then System 1 is stable.
-/
theorem Stability_of_Reducible
    (Red : ReducibleSystem M1 M2 Provable ωΓ encode_halt1 encode_halt2)
    (hKMono : RevHalt.DetectsMono K)
    (hStable2 : S1Rel Provable K M2 encode_halt2 ωΓ = ∅) :
    S1Rel Provable K M1 encode_halt1 ωΓ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem] at *
  intro s1 hIn1
  -- s1 ∈ S1Rel1 => ∃ p1, s1 = encode_halt1 p1 ∧ Rev0_K (M1 p1) ∧ ¬Provable(encode_halt1 p1)
  -- Note: S1Rel definition is: { s | ∃ c, s = encode_halt c ∧ Rev0_K (M c) ∧ ¬ Provable ... }
  rcases hIn1 with ⟨p1, rfl, hRev1, hNotProv1⟩

  -- Translate to System 2 via reduction
  let p2 := Red.toCode p1

  -- Step 1: Transfer Rev0 (Halting)
  -- hRev1 : Rev0_K K (M1 p1)
  -- We know Rev0_K <-> Halts (via DetectsMono)
  have hHalt1 : RevHalt.Halts (M1 p1) := by
    rw [← RevHalt.revK_iff_halts_of_DetectsMono K hKMono]
    exact hRev1

  have hHalt2 : RevHalt.Halts (M2 p2) := Red.halts_iff p1 |>.mp hHalt1

  have hRev2 : RevHalt.Rev0_K K (M2 p2) := by
    unfold RevHalt.Rev0_K
    rw [RevHalt.revK_iff_halts_of_DetectsMono K hKMono]
    exact hHalt2

  -- Step 2: Transfer Non-Provability
  -- hNotProv1 : ¬ Provable ωΓ (encode_halt1 p1)
  have hNotProv2 : ¬ Provable ωΓ (encode_halt2 p2) :=
    fun h => hNotProv1 (Red.provable_iff p1 |>.mpr h)

  -- Construct S1Rel member for System 2
  have hIn2 : encode_halt2 p2 ∈ S1Rel Provable K M2 encode_halt2 ωΓ := by
    refine ⟨p2, rfl, hRev2, hNotProv2⟩

  -- Contradiction with hStable2
  exact hStable2 (encode_halt2 p2) hIn2

end Invariance

end RevHalt
