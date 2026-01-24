/-
  CollatzBridge.lean

  Isolation of the Consistency Bridge proof.
  Goal: Prove `PA_implies_RouteIIAt`.
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Instances.CollatzWitnesses

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic

lemma bridge_proof : PA_implies_RouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) (PAax := PAax) := sorry

#print axioms bridge_proof

end RevHalt.Instances
