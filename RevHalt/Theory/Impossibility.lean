import RevHalt.Base
import RevHalt.Theory.Canonicity
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.Impossibility

T2: Impossibility of Internalizing Rev associated with a Canoncial Kit.

This file demonstrates that the "Real Halting" defined by a Canonical Kit (certified by T1)
cannot be fully captured by any internal logical predicate, provided the system supports
basic diagonalization.

## Explicit Dependencies
- `Trace` (Signal)
- `RHKit` (Observation Instrument)
- `DetectsMonotone` (Canonicity Condition)
- `Rev0_K` (The Truth being targeted)

-/

namespace RevHalt

/--
  `ImpossibleSystem`: A structure representing a logical system coupled with a Canonical Observation Kit.

  This structure explicitly bundles:
  1. The Physical Layer: `Machine` (Code -> Trace) and `K` (Kit).
  2. The Certification: `h_canon` proving the Kit is Monotone-Detecting (T1 applies).
  3. The Logical Layer: `Provable`, `Not`, etc.
  4. The Bridge: `diagonal_program` linking Logical Proof to Kit Truth (`Rev0_K`).
-/
structure ImpossibleSystem (Code : Type) (PropT : Type) where
  -- [A] The Physical/Dynamic Base
  Machine : Code → Trace
  K       : RHKit

  -- [B] The Canonicity Certificate
  h_canon : DetectsMonotone K

  -- [C] The Logical Layer
  Provable : PropT → Prop
  FalseT   : PropT
  Not      : PropT → PropT

  -- [D] Consistency Axioms
  consistent : ¬ Provable FalseT
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT

  -- [E] The Diagonal Fixpoint (Explicitly linking Rev0_K and Logic)
  -- "There exists a program e whose Universal Halting (Rev0_K) is equivalent to Provable(Not(H e))"
  diagonal_program : ∀ H : Code → PropT, ∃ e, Rev0_K K (Machine e) ↔ Provable (Not (H e))

/--
  Definition of an Internal Halting Predicate for an ImpossibleSystem.
  It tries to emulate the specific truth `Rev0_K S.K (S.Machine e)`.
-/
structure InternalHaltingPredicate {Code : Type} {PropT : Type} (S : ImpossibleSystem Code PropT) where
  H : Code → PropT
  total    : ∀ e, S.Provable (H e) ∨ S.Provable (S.Not (H e))
  correct  : ∀ e, Rev0_K S.K (S.Machine e) → S.Provable (H e)
  complete : ∀ e, ¬ Rev0_K S.K (S.Machine e) → S.Provable (S.Not (H e))

/--
  **Theorem T2**:
  No Internal Halting Predicate can exist for a Canonical ImpossibleSystem.

  This theorem relies explicitly on the `ImpossibleSystem` structure, ensuring that
  the impossibility is a direct consequence of the Kit's nature and the System's logic.
-/
theorem T2_impossibility {Code : Type} {PropT : Type} (S : ImpossibleSystem Code PropT) :
    ¬ ∃ _ : InternalHaltingPredicate S, True := by
  intro h
  obtain ⟨I, _⟩ := h

  -- 1. Construct the diagonal program e for the predicate I.H
  --    Using the explicit bridge in S: Rev0_K ... <-> Provable ...
  obtain ⟨e, he⟩ := S.diagonal_program I.H

  -- 2. Analyze by cases on the *real* truth of Rev0_K K (Machine e)
  by_cases hReal : Rev0_K S.K (S.Machine e)
  · -- Case: e really halts (Canonically)
    -- By Correctness, the system proves H(e)
    have hProvH : S.Provable (I.H e) := I.correct e hReal
    -- By Diagonal property, Provable(¬ H(e)) must be true
    have hProvNotH : S.Provable (S.Not (I.H e)) := he.mp hReal
    -- Contradiction in the system
    exact S.consistent (S.absurd (I.H e) hProvH hProvNotH)
  · -- Case: e does not halt (Canonically)
    -- By Completeness, the system proves ¬ H(e)
    have hProvNotH : S.Provable (S.Not (I.H e)) := I.complete e hReal
    -- By Diagonal property: Provable(¬ H(e)) -> Rev0_K ...
    have hImpliesReal : S.Provable (S.Not (I.H e)) → Rev0_K S.K (S.Machine e) := he.mpr
    have hRealContradiction : Rev0_K S.K (S.Machine e) := hImpliesReal hProvNotH
    -- Contradiction with hypothesis hReal
    exact hReal hRealContradiction

end RevHalt
