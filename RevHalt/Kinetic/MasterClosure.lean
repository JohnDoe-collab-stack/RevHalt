import RevHalt.Bridge.Context
import RevHalt.Kinetic.Closure

/-!
# RevHalt.Kinetic.MasterClosure

Master Theorem Enhanced with Kinetic Closure.

## Contents
- `VerifiableContext`: EnrichedContext + Dynamic Bridge
- `Master_Closure`: CloK is a strict superset of ProvableSet
- `TheGreatChain`: Truth ↔ CloK ↔ Halts ↔ Rev0_K
-/

namespace RevHalt

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

/--
  **The Great Chain of Equivalence**

  Unifies Truth, Kinetic Closure, Halting, and Observational Verdicts.
  We prove the conjunction of equivalences to establish mutual equivalence.

  $$ Truth(p) \iff p \in CloK \iff Halts(LR(p)) \iff Rev0_K(LR(p)) $$
-/
theorem TheGreatChain (ctx : VerifiableContext Code PropT)
    (K : RHKit) (hK : DetectsMonotone K) :
    ∀ p,
      (ctx.Truth p ↔ p ∈ CloK (LR := ctx.LR) ∅) ∧      -- 1 ↔ 2
      (p ∈ CloK (LR := ctx.LR) ∅ ↔ Halts (ctx.LR ∅ p)) ∧  -- 2 ↔ 3
      (Halts (ctx.LR ∅ p) ↔ Rev0_K K (ctx.LR ∅ p))         -- 3 ↔ 4
    := by
  intro p
  -- Link 1-2: Truth ↔ CloK (via Truth_is_CloK)
  have h1 : ctx.Truth p ↔ p ∈ CloK (LR := ctx.LR) ∅ := Truth_is_CloK ctx p

  -- Link 2-3: CloK ↔ Halts (Definition)
  have h2 : p ∈ CloK (LR := ctx.LR) ∅ ↔ Halts (ctx.LR ∅ p) := mem_CloK_iff (LR := ctx.LR) ∅ p

  -- Link 3-4: Halts ↔ Rev0_K (via T1 Canonicity)
  have h3 : Halts (ctx.LR ∅ p) ↔ Rev0_K K (ctx.LR ∅ p) := (T1_traces K hK (ctx.LR ∅ p)).symm

  exact ⟨h1, h2, h3⟩

-- ============================================================================
-- GapWitnessV: Operative form for VerifiableContext
-- ============================================================================

/--
**GapWitnessV**: Typed witness for VerifiableContext.

Same as GapWitness but for VerifiableContext, giving access to the bridge.
-/
def GapWitnessV (ctx : VerifiableContext Code PropT) : Type :=
  { p : PropT // ctx.Truth p ∧ ¬ctx.Provable p }

/--
**Gap witnesses exist for VerifiableContext** (via T2).
-/
theorem gapWitnessV_nonempty (ctx : VerifiableContext Code PropT) :
    Nonempty (GapWitnessV ctx) := by
  obtain ⟨p, hpT, hpNP⟩ := true_but_unprovable_exists ctx.toEnrichedContext
  exact ⟨⟨p, hpT, hpNP⟩⟩

/-- Extract the proposition from a gap witness. -/
def GapWitnessV.prop {ctx : VerifiableContext Code PropT} (w : GapWitnessV ctx) : PropT := w.1

/-- A gap witness is true. -/
theorem GapWitnessV.truth {ctx : VerifiableContext Code PropT} (w : GapWitnessV ctx) :
    ctx.Truth w.prop := w.2.1

/-- A gap witness is not provable. -/
theorem GapWitnessV.not_provable {ctx : VerifiableContext Code PropT} (w : GapWitnessV ctx) :
    ¬ctx.Provable w.prop := w.2.2

/--
**Operative form**: A gap witness halts (via bridge).

This is the "Collatz-like de Rev" object: a trace that halts but isn't provable.
-/
theorem gapWitnessV_halts (ctx : VerifiableContext Code PropT) :
    ∀ w : GapWitnessV ctx, Halts (ctx.LR ∅ w.prop) := by
  intro w
  exact (ctx.h_bridge w.prop).mp w.truth

end RevHalt
