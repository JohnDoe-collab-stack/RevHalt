import RevHalt.Base
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.Impossibility

T2: Impossibility of Internalizing Rev (Abstract Turing-Gödel synthesis).

## Main Results
- `TGAssumptions`: Structural assumptions (interface) for the impossibility result.
- `TG_of_Kit`: Explicit construction of these assumptions from a Kit.
- `InternalHaltingPredicate`: Total + Correct + Complete predicate.
- `T2_impossibility`: No such predicate can exist.
-/

namespace RevHalt

/--
  Hypothèses structurelles pour l'argument diagonal (T2).
  Ce n'est pas un axiome, mais une interface que le système doit satisfaire.

  Represents a computing system with:
  - `Code`: program codes
  - `PropT`: internal propositions / types
  - `RealHalts`: the external, "real" truth (provided by the Kit)
  - `Provable`: an internal provability predicate
  - `diagonal_program`: the ability to construct self-referential sentences
-/
structure TGAssumptions (Code : Type) (PropT : Type) where
  RealHalts : Code → Prop
  Provable  : PropT → Prop
  FalseT    : PropT
  Not       : PropT → PropT
  -- Consistency Axiom
  consistent : ¬ Provable FalseT
  -- Logic Axiom
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT
  -- Diagonal Fixpoint Axiom (The hardest part to satisfy)
  diagonal_program : ∀ H : Code → PropT, ∃ e, RealHalts e ↔ Provable (Not (H e))

/-- Backward compatibility alias. -/
abbrev TuringGodelContext' := TGAssumptions

/--
  Construction canonique des hypothèses TG depuis la couche Kit.

  Cette fonction rend explicite la dépendance : pour avoir un contexte T2 valide,
  il faut un Kit (pour définir `RealHalts`) et un substrat logique (pour la diagonalisation).
-/
def TG_of_Kit {Code PropT : Type}
  (K : RHKit)
  (Machine : Code → Trace)
  -- Logic backend
  (Provable : PropT → Prop)
  (FalseT : PropT)
  (Not : PropT → PropT)
  (consistent : ¬ Provable FalseT)
  (absurd : ∀ p, Provable p → Provable (Not p) → Provable FalseT)
  -- The diagonal lemma linked to the Kit's truth
  (diagonal : ∀ H : Code → PropT, ∃ e, Rev0_K K (Machine e) ↔ Provable (Not (H e)))
  : TGAssumptions Code PropT :=
  { RealHalts := fun e => Rev0_K K (Machine e)
  , Provable := Provable
  , FalseT := FalseT
  , Not := Not
  , consistent := consistent
  , absurd := absurd
  , diagonal_program := diagonal
  }

/--
  Definition of an Internal Halting Predicate within the assumptions.
  To be a candidate for "capturing" RealHalts, it must be:
  1. Total (always proves Yes or No).
  2. Correct (if leads to Yes, it really halts).
  3. Complete (if leads to No, it really doesn't halt).
-/
structure InternalHaltingPredicate {Code : Type} {PropT : Type} (ctx : TGAssumptions Code PropT) where
  H : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))

/--
  **Theorem T2**:
  There is no internal predicate I that is simultaneously Total, Correct, and Complete
  with respect to RealHalts (as defined by the abstract assumptions).
-/
theorem T2_impossibility {Code : Type} {PropT : Type} (ctx : TGAssumptions Code PropT) :
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
