/-
  ConcreteBridgeMin.lean

  Phase E glue (dynamic bridge only):
  - Takes a minimal witness bundle (AssumptionsD)
  - Takes direct Route-II hypotheses on Collatz
  - Produces a concrete CollatzInstance
-/

import RevHalt.Instances.ConcreteCollatz
import RevHalt.Instances.CollatzBridge

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic

/--
  Build a concrete instance from:
  - minimal Collatz witness assumptions (A)
  - dynamic bridge data on Collatz
-/
def ConcreteInstance_min_with_bridge
    (A : CollatzWitnessesAssumptionsD)
    (hSound : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ)
    (hNegComp : NegativeComplete K Machine encode_halt
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hDec : ∀ e, Decidable
      ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e)))
    (hBarrier :
      (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) →
        False) :
    CollatzInstance :=
  ConcreteInstance (CollatzWitnessesData_of_AssumptionsD A)
    (CollatzBridgeAssumptions_of_AssumptionsD A hSound hNegComp hDec hBarrier)

/--
  Packaged dynamic assumptions: enough to build a concrete CollatzInstance
  without axioms/sorry.
-/
structure ConcreteBridgeAssumptionsD where
  A : CollatzWitnessesAssumptionsD
  hSound : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
    (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ
  hNegComp : NegativeComplete K Machine encode_halt
    (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
    (CollatzWitnessesData_of_AssumptionsD A).SNot_PA
  hDec : ∀ e, Decidable
    ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))
  hBarrier :
    (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) →
      False

def ConcreteInstance_of_D (D : ConcreteBridgeAssumptionsD) : CollatzInstance :=
  ConcreteInstance_min_with_bridge D.A D.hSound D.hNegComp D.hDec D.hBarrier

/-- Convenience alias (dynamic-only). -/
def ConcreteInstance_min_dynamic
    (A : CollatzWitnessesAssumptionsD)
    (hSound : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ)
    (hNegComp : NegativeComplete K Machine encode_halt
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hDec : ∀ e, Decidable
      ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e)))
    (hBarrier :
      (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) →
        False) :
    CollatzInstance :=
  ConcreteInstance_min_with_bridge A hSound hNegComp hDec hBarrier

end RevHalt.Instances
