/-
  ConcreteBridgeMin.lean

  Phase E glue:
  - Takes a minimal witness bundle (AssumptionsD)
  - Takes explicit bridge hypotheses (universal machine, richness, T2 data)
  - Produces a concrete CollatzInstance via ConcreteInstance_min
-/

import RevHalt.Instances.ConcreteCollatz
import RevHalt.Instances.CollatzBridge

namespace RevHalt.Instances

open Nat.Partrec
open RevHalt.Trilemma.Generic

/--
  Build a concrete instance from:
  - minimal Collatz witness assumptions (A)
  - explicit universal-machine bridge data
-/
def ConcreteInstance_min_with_bridge
    (A : CollatzWitnessesAssumptionsD)
    (encode_U : UCode → PropT)
    (richness_bridge_axiom : ∀ {Γ : Set PropT},
      S1Rel (CollatzWitnessesData_of_AssumptionsD A).Provable K Machine encode_halt Γ = ∅ →
      S1Rel (CollatzWitnessesData_of_AssumptionsD A).Provable K UMachine encode_U Γ = ∅)
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
      encode_U richness_bridge_axiom hSound_U hNegComp_U hTotal_U f_U hf_U hsemidec_U
      S_PA_consistent S_PA_absurd)

/--
  Packaged option-1 assumptions: a single bundle that is enough
  to build a concrete CollatzInstance without axioms/sorry.
-/
structure ConcreteBridgeAssumptionsD where
  A : CollatzWitnessesAssumptionsD
  encode_U : UCode → PropT
  richness_bridge_axiom : ∀ {Γ : Set PropT},
    S1Rel (CollatzWitnessesData_of_AssumptionsD A).Provable K Machine encode_halt Γ = ∅ →
    S1Rel (CollatzWitnessesData_of_AssumptionsD A).Provable K UMachine encode_U Γ = ∅
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
  ConcreteInstance_min_with_bridge D.A D.encode_U D.richness_bridge_axiom
    D.hSound_U D.hNegComp_U D.hTotal_U D.f_U D.hf_U D.hsemidec_U
    D.S_PA_consistent D.S_PA_absurd

end RevHalt.Instances
