/-
  CollatzBridge.lean

  Isolation of the Consistency Bridge proof.
  Goal: Prove `PA_implies_RouteIIAt`.
-/

import RevHalt.Trilemma.CollatzDynamicPA -- Import definition of PA_implies_RouteIIAt (via Generic)
import RevHalt.Instances.CollatzWitnesses -- Import limits/context

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic

axiom bridge_proof : PA_implies_RouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) (PAax := PAax)

#print axioms bridge_proof

end RevHalt.Instances
