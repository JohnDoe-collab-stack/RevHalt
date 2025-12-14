/-
  RevHalt.Unified.MasterClosure

  Master Theorem Enhanced with Kinetic Closure.

  This module connects the abstract T1/T2/T3 results to the Closure framework.
  It characterizes the incompleteness gap dynamically:

  "True but Unprovable" ↔ "Kinetically Verifiable but Statically Unprovable"

  ## Main Theorem: `Master_Closure`
  If a Dynamic Bridge exists (Truth ↔ Halts(LR)):
  1. Provable ⊆ CloK (All theorems are verifiable)
  2. CloK \ Provable ≠ ∅ (There are verifiable truths that are unprovable)
-/

import RevHalt.Unified.Core
import RevHalt.Unified.Closure

namespace RevHalt_Unified

variable {Code PropT : Type}
variable {LR : Set PropT → PropT → Trace}

/--
  Enriched Context + Dynamic Bridge.
  We assume the generic `DynamicBridge` holds for the Truth predicate:
  `Truth p ↔ Halts (LR ∅ p)`
  (We use ∅ context for absolute truth).
-/
structure VerifiableContext (Code PropT : Type) extends EnrichedContext Code PropT where
  /-- Local reading function -/
  LR : Set PropT → PropT → Trace
  /-- Bridge: Truth corresponds to halting of the empty-context trace -/
  h_bridge : ∀ p, Truth p ↔ Halts (LR ∅ p)

/--
  **Master Closure Theorem**

  Shows that `CloK` (Kinetic Closure) is a strict superset of `ProvableSet`.
  The "gap" is exactly the set of kinetically verifiable truths.
-/
theorem Master_Closure
    (ctx : VerifiableContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    let CloK_empty := CloK (LR := ctx.LR) ∅
    -- (1) Soundness: Provable ⊆ Verifiable
    (ProvableSet ctx.toEnrichedContext ⊆ CloK_empty) ∧
    -- (2) Strictness: Verifiable \ Provable ≠ ∅
    (∃ p, p ∈ CloK_empty ∧ p ∉ ProvableSet ctx.toEnrichedContext) := by

  let CloK_empty := CloK (LR := ctx.LR) ∅

  constructor
  · -- (1) Provable ⊆ CloK
    intro p hProv
    -- p is Provable => p is True (by Soundness)
    have hTrue : ctx.Truth p := h_sound p hProv
    -- p is True => Halts (LR ∅ p) (by Bridge)
    have hHalts : Halts (ctx.LR ∅ p) := (ctx.h_bridge p).mp hTrue
    -- Halts (LR ∅ p) => p ∈ CloK (by definition)
    -- We use mem_CloK_iff from Closure
    rw [mem_CloK_iff (LR := ctx.LR)]
    exact hHalts

  · -- (2) Use T2 to find the witness
    obtain ⟨p, hTrue, hNotProv⟩ := true_but_unprovable_exists ctx.toEnrichedContext
    use p
    constructor
    · -- p is True => p ∈ CloK (via Bridge)
      have hHalts : Halts (ctx.LR ∅ p) := (ctx.h_bridge p).mp hTrue
      rw [mem_CloK_iff (LR := ctx.LR)]
      exact hHalts
    · -- p is not Provable
      exact hNotProv

/--
  **Corollary**: The set of truths is exactly CloK.
  This gives a computational characterization of Truth.
-/
theorem Truth_is_CloK (ctx : VerifiableContext Code PropT) :
    ∀ p, ctx.Truth p ↔ p ∈ CloK (LR := ctx.LR) ∅ := by
  intro p
  constructor
  · -- Truth -> CloK
    intro hTrue
    have hHalts := (ctx.h_bridge p).mp hTrue
    rw [mem_CloK_iff (LR := ctx.LR)]
    exact hHalts
  · -- CloK -> Truth
    intro hCloK
    rw [mem_CloK_iff (LR := ctx.LR)] at hCloK
    exact (ctx.h_bridge p).mpr hCloK

end RevHalt_Unified
