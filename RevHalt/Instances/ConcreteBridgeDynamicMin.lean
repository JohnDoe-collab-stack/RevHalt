/-
  ConcreteBridgeDynamicMin.lean

  Phase E glue (dynamic bridge, no universal compilation):
  - Takes a minimal witness bundle (AssumptionsD)
  - Takes Route II "barrier" hypotheses for the same Collatz machine
  - Produces a concrete `Generic.CollatzInstance`

  This removes the "Collatz -> universal machine" reduction layer.
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Instances.CollatzWitnesses
import RevHalt.Instances.CollatzBridge

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic

/--
Build a concrete instance from:
- minimal Collatz witness assumptions (A)
- dynamic Route II hypotheses for the Collatz machine (Soundness, NegComp, Dec, Barrier)

No universal machine / compiler is used here.
-/
def ConcreteInstance_min_dynamic
    (A : CollatzWitnessesAssumptionsD)
    (hSound :
      ∀ Γ,
        Soundness
          (CollatzWitnessesData_of_AssumptionsD A).Provable
          (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
          Γ)
    (hNegComp :
      NegativeComplete K Machine encode_halt
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hDec :
      ∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e)))
    (hBarrier :
      (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) → False) :
    CollatzInstance :=
  let W := CollatzWitnessesData_of_AssumptionsD A
  { PropT       := PropT
    Code        := Code
    Provable    := W.Provable
    K           := K
    Machine     := Machine
    encode_halt := encode_halt
    Cn          := W.Cn
    A0          := W.A0
    PAax        := W.PAax
    hIdem       := W.hIdem
    hProvCn     := W.hProvCn
    hMono       := W.hMono
    hCnExt      := W.hCnExt
    witBC       := W.witBC
    witAC       := W.witAC
    witAB       := W.witAB
    bridge      := bridge_proof_dynamic W hSound hNegComp hDec hBarrier }

/-- Packaged dynamic assumptions: enough to build a concrete CollatzInstance. -/
structure ConcreteBridgeDynamicAssumptionsD where
  A : CollatzWitnessesAssumptionsD
  hSound :
    ∀ Γ,
      Soundness
        (CollatzWitnessesData_of_AssumptionsD A).Provable
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        Γ
  hNegComp :
    NegativeComplete K Machine encode_halt
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA
  hDec :
    ∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))
  hBarrier :
    (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) → False

def ConcreteInstance_of_dynamic_D (D : ConcreteBridgeDynamicAssumptionsD) : CollatzInstance :=
  ConcreteInstance_min_dynamic D.A D.hSound D.hNegComp D.hDec D.hBarrier

end RevHalt.Instances

