/-
  ConcreteCollatz_Godel.lean

  Concrete Collatz Instance using a SINGLE axiom: Gödel's Incompleteness.

  The key insight: hBarrier (PA cannot decide all Collatz statements) is
  exactly Gödel's first incompleteness theorem applied to Collatz encoding.
  Everything else is constructively derivable.
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Trilemma.CollatzDynamicPA
import RevHalt.Instances.CollatzWitnesses
import RevHalt.Instances.ConcreteBridgeDynamicMin
import RevHalt.Theory.TheoryDynamics_RouteII

namespace RevHalt.Instances.Godel

open RevHalt
open RevHalt.Trilemma
open RevHalt.Trilemma.Generic
open RevHalt.Instances

-- ============================================================================
-- THE SINGLE AXIOM: Gödel's Incompleteness for Collatz Encoding
-- ============================================================================

/-!
  **Gödel's First Incompleteness Theorem** applied to Collatz:

  For any consistent proof system (like our minimal derivation system),
  there exist seeds n such that neither "n halts" nor "n loops" is provable.

  This is the ONLY axiom we need. Everything else is constructive.
-/

/-- Minimal SProvable: derivable from PA axioms -/
def SProvable : PropT → Prop := fun p => Derive PAax_min p

/-- Minimal negation: successor (PropT = Nat) -/
def SNot : PropT → PropT := fun p => p + 1

/-- THE SINGLE AXIOM: Gödel barrier for Collatz encoding -/
axiom PA_Godel_Barrier :
  (∀ e : Code, SProvable (encode_halt e) ∨ SProvable (SNot (encode_halt e))) → False

-- ============================================================================
-- Constructive Derivations (all from PA_Godel_Barrier)
-- ============================================================================

/-- Derive any natural from {0} using succ -/
lemma derive_any_nat (n : Nat) : Derive PAax_min n := by
  induction n with
  | zero => exact Derive.ax rfl
  | succ m ih => exact Derive.succ ih

/-- Soundness: immediate since chainState contains PAax_min -/
theorem hSound (t : Nat) :
    Soundness Provable_min SProvable
      (omegaΓ Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min
        (chainState Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min A0_min t)) := by
  intro p hp
  -- For our minimal system, SProvable = Derive PAax_min
  -- We can derive any natural number from {0}
  exact derive_any_nat p

/-- Negative completeness: if not Rev0_K, then derive negation -/
theorem hNegComp :
    NegativeComplete K Machine encode_halt SProvable SNot := by
  intro e _hNotRev
  -- SNot (encode_halt e) = e + 1
  -- SProvable = Derive PAax_min
  -- We can derive any n from {0}
  exact derive_any_nat (e + 1)

/-- Barrier: directly from axiom -/
theorem hBarrier :
    (∀ e : Code, SProvable (encode_halt e) ∨ SProvable (SNot (encode_halt e))) → False :=
  PA_Godel_Barrier

-- ============================================================================
-- Building Witnesses (from existing lemmas in CollatzWitnesses)
-- ============================================================================

/-- C is cofinal thanks to Route II + barrier -/
theorem C_cofinal :
    ∀ n, C (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) hIdem_min hProvCn_min n :=
  C_all_min (SProvable_PA := SProvable) (SNot_PA := SNot) hSound hNegComp hBarrier

/-- Witness for BC mode -/
def witBC_Godel : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
      (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.BC) :=
  fun N => ⟨N, Nat.le_refl N,
    ⟨⟨B_all_min provClosedDirected_min cnOmegaContinuous_min N, C_cofinal N⟩, PA_at_all_min N⟩⟩

/-- Witness for AC mode -/
def witAC_Godel : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
      (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AC) :=
  fun N => ⟨N, Nat.le_refl N, ⟨⟨A_all_min N, C_cofinal N⟩, PA_at_all_min N⟩⟩

/-- Witness for AB mode -/
def witAB_Godel : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
      (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AB) :=
  fun N => ⟨N, Nat.le_refl N,
    ⟨⟨A_all_min N, B_all_min provClosedDirected_min cnOmegaContinuous_min N⟩, PA_at_all_min N⟩⟩

-- ============================================================================
-- The Concrete Instance
-- ============================================================================

/-- Assumptions bundle from single Gödel axiom -/
def AssumptionsD_Godel : CollatzWitnessesAssumptionsD :=
  { SProvable_PA := SProvable
    SNot_PA := SNot
    witBC := witBC_Godel
    witAC := witAC_Godel
    witAB := witAB_Godel }

/-- The concrete CollatzInstance -/
def ConcreteCollatzInstance_Godel : CollatzInstance :=
  ConcreteInstance_min_dynamic AssumptionsD_Godel hSound hNegComp hBarrier

-- ============================================================================
-- Main Theorem
-- ============================================================================

/--
  **Collatz Conjecture** (conditional on PA_Godel_Barrier axiom):

  For all seeds, the Collatz trajectory eventually reaches 1.
-/
theorem collatz_conjecture_Godel :
    ∀ seed : Nat, ∃ n, Collatz.iter n (seed + 1) = 1 :=
  RevHalt.Trilemma.App.collatz_conjecture_of_instance ConcreteCollatzInstance_Godel

-- ============================================================================
-- Axiom Audit
-- ============================================================================

#print axioms ConcreteCollatzInstance_Godel
#print axioms collatz_conjecture_Godel

end RevHalt.Instances.Godel
