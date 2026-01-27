/-
  ConcreteDynamicInstance.lean

  One-stop construction (no universal-machine bridge):
  - assumes Route-II "dynamic" hypotheses for the *Collatz machine* layer
  - builds the cofinal witnesses (BC/AC/AB) from the `PairPA_all_min_*` lemmas
  - packages everything into `Generic.CollatzInstance`
  - exposes the Collatz conclusion (for positive seeds) via `CollatzDynamicPA`
-/

import RevHalt.Instances.CollatzWitnesses
import RevHalt.Instances.ConcreteBridgeDynamicMin
import RevHalt.Trilemma.CollatzDynamicPA

namespace RevHalt.Instances

open RevHalt.Trilemma
open RevHalt.Trilemma.Generic

/-!
## Build witness bundle A (AssumptionsD) from dynamic Route-II hypotheses

This eliminates the need to postulate the 3 cofinal witnesses separately.
-/

def CollatzWitnessesAssumptionsD_of_dynamic
    (SProvable_PA : PropT -> Prop)
    (SNot_PA : PropT -> PropT)
    (hSound : forall G, Soundness Provable_min SProvable_PA G)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : forall e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (forall e, Decidable (SProvable_PA (encode_halt e))) -> False) :
    CollatzWitnessesAssumptionsD :=
  let witBC : CofinalWitness
      (PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min)
        PAax_min Mode.BC) :=
    witness_of_forall
      (PairPA_all_min_BC
        (hPCdir := provClosedDirected_min) (hω := cnOmegaContinuous_min)
        (SProvable_PA := SProvable_PA) (SNot_PA := SNot_PA)
        (hSound := hSound) (hNeg := hNeg) (hDec := hDec) (hBar := hBar))
  let witAC : CofinalWitness
      (PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min)
        PAax_min Mode.AC) :=
    witness_of_forall
      (PairPA_all_min_AC
        (SProvable_PA := SProvable_PA) (SNot_PA := SNot_PA)
        (hSound := hSound) (hNeg := hNeg) (hDec := hDec) (hBar := hBar))
  let witAB : CofinalWitness
      (PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min)
        PAax_min Mode.AB) :=
    witness_of_forall
      (PairPA_all_min_AB (hPCdir := provClosedDirected_min) (hω := cnOmegaContinuous_min))
  CollatzWitnessesAssumptionsD_min SProvable_PA SNot_PA witBC witAC witAB


/-!
## Build a `ConcreteBridgeDynamicAssumptionsD` directly
-/

def ConcreteBridgeDynamicAssumptionsD_of_dynamic
    (SProvable_PA : PropT -> Prop)
    (SNot_PA : PropT -> PropT)
    (hSound : forall G, Soundness Provable_min SProvable_PA G)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : forall e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (forall e, Decidable (SProvable_PA (encode_halt e))) -> False) :
    ConcreteBridgeDynamicAssumptionsD :=
  let A := CollatzWitnessesAssumptionsD_of_dynamic
    (SProvable_PA := SProvable_PA) (SNot_PA := SNot_PA) hSound hNeg hDec hBar
  { A := A
    hSound := by
      intro G
      -- W.Provable = Provable_min for the minimal package.
      simpa [CollatzWitnessesData_of_AssumptionsD, CollatzWitnessesMinimal] using (hSound G)
    hNegComp := by
      -- Same comment: the fields are definitional reductions to the minimal package.
      simpa [CollatzWitnessesData_of_AssumptionsD, CollatzWitnessesMinimal] using hNeg
    hDec := by
      intro e
      simpa [CollatzWitnessesData_of_AssumptionsD, CollatzWitnessesMinimal] using (hDec e)
    hBarrier := by
      intro hdecAll
      -- `hdecAll` is definitional equal to the assumed decidability.
      exact hBar (fun e => by simpa using (hdecAll e)) }


/-!
## Collatz consequence (positive seeds) from the dynamic package
-/

theorem collatz_conjecture_of_dynamic
    (SProvable_PA : PropT -> Prop)
    (SNot_PA : PropT -> PropT)
    (hSound : forall G, Soundness Provable_min SProvable_PA G)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : forall e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (forall e, Decidable (SProvable_PA (encode_halt e))) -> False) :
    forall seed : Nat, exists n, Collatz.iter n (seed + 1) = 1 := by
  let D :=
    ConcreteBridgeDynamicAssumptionsD_of_dynamic
      (SProvable_PA := SProvable_PA) (SNot_PA := SNot_PA) hSound hNeg hDec hBar
  exact RevHalt.Trilemma.App.collatz_conjecture_of_instance (I := ConcreteInstance_of_dynamic_D D)

end RevHalt.Instances
