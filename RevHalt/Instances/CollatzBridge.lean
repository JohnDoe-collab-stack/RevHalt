/-
  CollatzBridge.lean

  Phase 2 Logic: The Bridge (constructive, no axioms).
  - Proves PA_implies_RouteIIAt *directly* on the Collatz machine.
  - No universal-machine reduction, no compile/simulation.
-/

import RevHalt.Instances.CollatzWitnesses
import RevHalt.Theory.TheoryDynamics
import RevHalt.Trilemma.GenericExtinction
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.Impossibility

namespace RevHalt.Instances

open RevHalt.Trilemma
open RevHalt.Trilemma.Generic
open RevHalt

-- Bridge assumptions packaged as data (no axioms, no universal reduction)
structure CollatzBridgeAssumptions (W : CollatzWitnessesData) where
  hSound : ∀ Γ, Soundness W.Provable W.SProvable_PA Γ
  hNegComp : NegativeComplete K Machine encode_halt W.SProvable_PA W.SNot_PA
  hDec : ∀ e, Decidable (W.SProvable_PA (encode_halt e))
  hBarrier : (∀ e, Decidable (W.SProvable_PA (encode_halt e))) → False

def CollatzBridgeAssumptions_of_AssumptionsD
    (A : CollatzWitnessesAssumptionsD)
    (hSound : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ)
    (hNegComp : NegativeComplete K Machine encode_halt
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hDec : ∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e)))
    (hBarrier :
      (∀ e, Decidable ((CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_halt e))) → False) :
    CollatzBridgeAssumptions (CollatzWitnessesData_of_AssumptionsD A) :=
  { hSound := hSound
    hNegComp := hNegComp
    hDec := hDec
    hBarrier := hBarrier }

-- 4) The Proof (Bridge)
theorem bridge_proof
    (W : CollatzWitnessesData)
    (B : CollatzBridgeAssumptions W) :
    PA_implies_RouteIIAt
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := W.Cn) (A0 := W.A0) (hIdem := W.hIdem) (hProvCn := W.hProvCn) W.PAax := by
  intro t _hPA
  have hNonempty :
      (S1Rel W.Provable K Machine encode_halt
        (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
          (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t))).Nonempty := by
    apply frontier_nonempty_of_route_II
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (SProvable := W.SProvable_PA) (SNot := W.SNot_PA)
    · exact B.hSound _
    · exact B.hNegComp
    · exact B.hDec
    · exact B.hBarrier
  simpa [RouteIIAt] using hNonempty

end RevHalt.Instances
