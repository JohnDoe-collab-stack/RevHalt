import RevHalt.Base
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.Impossibility

T2: Impossibility of Internalizing Rev (Abstract Turing-Gödel synthesis).

## Main Results
- `TuringGodelContext'`: Abstract context unifying Turing and Gödel
- `InternalHaltingPredicate`: Total + Correct + Complete predicate
- `T2_impossibility`: No such predicate can exist
-/

namespace RevHalt

/--
  Context for the impossibility result.
  Represents a computing system with:
  - `Code`: program codes
  - `PropT`: internal propositions / types
  - `RealHalts`: the external, "real" truth (e.g., our Rev0_K)
  - `Provable`: an internal provability predicate
  - `diagonal_program`: the ability to construct self-referential sentences
-/
structure TuringGodelContext' (Code : Type) (PropT : Type) where
  RealHalts : Code → Prop
  Provable  : PropT → Prop
  FalseT    : PropT
  Not       : PropT → PropT
  -- Consistency Axiom
  consistent : ¬ Provable FalseT
  -- Logic Axiom
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT
  -- Diagonal Fixpoint Axiom
  diagonal_program : ∀ H : Code → PropT, ∃ e, RealHalts e ↔ Provable (Not (H e))

/--
  Definition of an Internal Halting Predicate.
  To be a candidate for "capturing" RealHalts, it must be:
  1. Total (always proves Yes or No).
  2. Correct (if leads to Yes, it really halts).
  3. Complete (if leads to No, it really doesn't halt).
-/
structure InternalHaltingPredicate {Code : Type} {PropT : Type} (ctx : TuringGodelContext' Code PropT) where
  H : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))

/--
  **Theorem T2**:
  There is no internal predicate I that is simultaneously Total, Correct, and Complete
  with respect to RealHalts.
-/
theorem T2_impossibility {Code : Type} {PropT : Type} (ctx : TuringGodelContext' Code PropT) :
    ¬ ∃ _ : InternalHaltingPredicate ctx, True := by
  intro h
  obtain ⟨I, _⟩ := h
  -- 1. Construct the diagonal program e for the predicate I.H
  --    Property: RealHalts(e) ↔ Provable(¬ I.H(e))
  obtain ⟨e, he⟩ := ctx.diagonal_program I.H

  -- 2. Analyze by cases on the *real* truth of Halts(e)
  by_cases hReal : ctx.RealHalts e
  · -- Case: e really halts
    -- By Correctness, the system proves H(e)
    have hProvH : ctx.Provable (I.H e) := I.correct e hReal
    -- By Diagonal property, since RealHalts(e) is true, Provable(¬ H(e)) must be true
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := he.mp hReal
    -- Contradiction in the system
    exact ctx.consistent (ctx.absurd (I.H e) hProvH hProvNotH)
  · -- Case: e does not halt
    -- By Completeness, the system proves ¬ H(e)
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := I.complete e hReal
    -- By Diagonal property: Provable(¬ H(e)) → RealHalts(e)
    have hImpliesReal : ctx.Provable (ctx.Not (I.H e)) → ctx.RealHalts e := he.mpr
    have hRealContradiction : ctx.RealHalts e := hImpliesReal hProvNotH
    -- Contradiction with hypothesis hReal
    exact hReal hRealContradiction

end RevHalt
