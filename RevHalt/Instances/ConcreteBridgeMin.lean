/-
  ConcreteBridgeMin.lean

  Phase E glue (classical T2 bridge):
  - Takes a minimal witness bundle (AssumptionsD)
  - Takes an explicit compile/simulation Collatz → universal machine
  - Takes standard T2 hypotheses (Soundness, NegComp, Total, semidec, PA consistency)
  - Produces a concrete CollatzInstance
-/

import RevHalt.Instances.ConcreteCollatz
import RevHalt.Instances.CollatzBridge

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic
open Nat.Partrec

/--
  Build a concrete instance from:
  - minimal Collatz witness assumptions (A)
  - explicit reduction to the universal machine
  - classical T2 hypotheses (Soundness, NegComp, Total, semidec, PA consistency)
-/
def ConcreteInstance_min_with_bridge
    (A : CollatzWitnessesAssumptionsD)
    (encode_U : UCode → PropT)
    (compile : UCode → Code)
    (hEncode : ∀ c, encode_U c = encode_halt (compile c))
    (hUpEqv : ∀ c, UpEqv (UMachine c) (Machine (compile c)))
    (hSound_U : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ)
    (hNegComp_U : NegativeComplete K UMachine encode_U
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hTotal_U : ∀ e, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_U e) ∨
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U e)))
    (f_U : UCode → (Nat →. Nat))
    (hf_U : Partrec (fun p : UCode × Nat => f_U p.1 p.2))
    (hsemidec_U :
      ∀ c, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U c)) ↔
        (∃ x : Nat, x ∈ (f_U c) 0))
    (S_PA_consistent : ¬ (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat))
    (S_PA_absurd :
      ∀ p, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA p →
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
          ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA p) →
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat)) :
    CollatzInstance :=
  ConcreteInstance (CollatzWitnessesData_of_AssumptionsD A)
    (CollatzBridgeAssumptions_of_AssumptionsD A
      encode_U compile hEncode hUpEqv
      hSound_U hNegComp_U hTotal_U f_U hf_U hsemidec_U
      S_PA_consistent S_PA_absurd)

/--
  Packaged classical T2 assumptions: enough to build a concrete CollatzInstance.
-/
structure ConcreteBridgeAssumptionsD where
  A : CollatzWitnessesAssumptionsD
  encode_U : UCode → PropT
  compile : UCode → Code
  hEncode : ∀ c, encode_U c = encode_halt (compile c)
  hUpEqv : ∀ c, UpEqv (UMachine c) (Machine (compile c))
  hSound_U : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
    (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ
  hNegComp_U : NegativeComplete K UMachine encode_U
    (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
    (CollatzWitnessesData_of_AssumptionsD A).SNot_PA
  hTotal_U : ∀ e, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_U e) ∨
    (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U e))
  f_U : UCode → (Nat →. Nat)
  hf_U : Partrec (fun p : UCode × Nat => f_U p.1 p.2)
  hsemidec_U :
    ∀ c, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U c)) ↔
      (∃ x : Nat, x ∈ (f_U c) 0)
  S_PA_consistent : ¬ (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat)
  S_PA_absurd :
    ∀ p, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA p →
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA p) →
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat)

def ConcreteInstance_of_D (D : ConcreteBridgeAssumptionsD) : CollatzInstance :=
  ConcreteInstance_min_with_bridge D.A D.encode_U D.compile D.hEncode D.hUpEqv
    D.hSound_U D.hNegComp_U D.hTotal_U D.f_U D.hf_U D.hsemidec_U
    D.S_PA_consistent D.S_PA_absurd

end RevHalt.Instances
