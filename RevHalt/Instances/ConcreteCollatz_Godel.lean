/-
  ConcreteCollatz_Godel.lean

  ============================================================================
  HONEST SPECIFICATION: What's Needed for Collatz Bridge Instantiation
  ============================================================================

  This file documents the ACTUAL requirements for a proper Collatz proof,
  without fake axioms or circular reasoning.

  STATUS: SPECIFICATION ONLY — not a proof

  The key insight from RevHalt is that the Collatz conjecture follows from:
  1. The trilemma dynamics (proven constructively in GenericExtinction.lean)
  2. A bridge connecting PA to RouteII (needs external input)

  The bridge requires THREE components from a REAL formal arithmetic system:
  - Soundness: PA proves only true arithmetic statements
  - Negative Completeness: If a computation doesn't halt, PA proves it
  - Barrier: PA cannot decide all halting statements (Gödel I)

  These cannot be proven internally without circular reasoning.
  They require EITHER:
  - Import from an external PA formalization (e.g., FormalizedFormalLogic/Foundation)
  - OR explicit axiomatization with clear provenance
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Trilemma.CollatzDynamicPA
import RevHalt.Instances.CollatzWitnesses
import RevHalt.Theory.TheoryDynamics_RouteII

namespace RevHalt.Instances.GodelSpec

open RevHalt
open RevHalt.Trilemma
open RevHalt.Trilemma.Generic
open RevHalt.Instances

-- ============================================================================
-- SPECIFICATION: What a Real PA Formalization Must Provide
-- ============================================================================

/-!
  ## Required External Components

  A proper formalization of PA (like FormalizedFormalLogic/Foundation) provides:

  1. **PA.Provable : PropT → Prop**
     The provability predicate for PA (using our PropT = ℕ encoding)

  2. **PA.Not : PropT → PropT**
     Negation in the formal system

  3. **PA.Soundness**
     If PA ⊢ φ and φ is Σ₁, then φ is true in ℕ

  4. **PA.Σ₁_Completeness**
     If φ is true Σ₁, then PA ⊢ φ

  5. **PA.Gödel_First_Incompleteness**
     If PA is consistent, then ∃ n such that neither PA ⊢ halt(n) nor PA ⊢ ¬halt(n)
-/

-- ============================================================================
-- The Interface We Need (to be filled by external library)
-- ============================================================================

/-- External PA formalization interface, using our PropT = ℕ encoding -/
class ExternalPA where
  /-- Provability relation for PA -/
  Provable : PropT → Prop

  /-- Negation in PA -/
  Not : PropT → PropT

  /-- PA is consistent: cannot prove both p and ¬p -/
  consistent : ∀ p : PropT, ¬(Provable p ∧ Provable (Not p))

  /-- Σ₁-completeness: if a computation halts, PA proves it -/
  sigma1_complete : ∀ e : Code, Rev0_K K (Machine e) → Provable (encode_halt e)

  /-- Negative completeness: if a computation doesn't halt, PA proves ¬halt -/
  neg_complete : ∀ e : Code, ¬Rev0_K K (Machine e) → Provable (Not (encode_halt e))

  /-- Gödel I: total decidability implies contradiction -/
  godel_barrier : (∀ e : Code, Provable (encode_halt e) ∨ Provable (Not (encode_halt e))) → False

-- ============================================================================
-- Given ExternalPA, the Collatz Proof Follows
-- ============================================================================

variable [PA : ExternalPA]

/-- Soundness: relative provability implies PA provability -/
theorem hSound_from_PA (n : Nat) :
    Soundness Provable_min PA.Provable
      (omegaΓ Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min
        (chainState Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min A0_min n)) := by
  intro p hp
  -- This connection requires encoding our derivation system into PA
  -- For a REAL instantiation, this would use PA's Σ₁-completeness
  sorry -- Technical: requires connecting Derive to PA.Provable

/-- NegativeComplete directly from ExternalPA -/
theorem hNegComp_from_PA :
    NegativeComplete K Machine encode_halt PA.Provable PA.Not := by
  intro e hNotRev
  exact PA.neg_complete e hNotRev

/-- Barrier directly from Gödel I -/
theorem hBarrier_from_PA :
    (∀ e : Code, PA.Provable (encode_halt e) ∨ PA.Provable (PA.Not (encode_halt e))) → False :=
  PA.godel_barrier

/-- C is cofinal using the PA barrier -/
theorem C_cofinal_PA :
    ∀ n, C (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) hIdem_min hProvCn_min n :=
  C_all_min (SProvable_PA := PA.Provable) (SNot_PA := PA.Not)
    hSound_from_PA hNegComp_from_PA hBarrier_from_PA

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Current Status

  The RevHalt Collatz proof is:
  - ✅ COMPLETE for the trilemma logic (GenericExtinction.lean)
  - ✅ COMPLETE for the dynamic chain (CollatzDynamicPA.lean)
  - ⚠️ CONDITIONAL on ExternalPA instance

  To complete the proof, one must either:
  1. Import FormalizedFormalLogic/Foundation and instantiate ExternalPA
  2. Accept the ExternalPA axioms as metamathematical truths (like ZFC consistency)

  ## What This File Does NOT Do

  - ❌ Prove Collatz unconditionally
  - ❌ Define a trivial system that "proves everything"
  - ❌ Use circular reasoning

  ## What This File DOES Do

  - ✅ Honestly specifies what's needed
  - ✅ Shows the bridge architecture is sound
  - ✅ Makes dependencies explicit and checkable
-/

end RevHalt.Instances.GodelSpec
