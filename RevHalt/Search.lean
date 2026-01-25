import RevHalt.Trilemma.GenericExtinction
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Instances.CollatzWitnesses -- To see if I can find witnesses relative to the instance context (if logic was declared)
-- But I'll use generic search.

open RevHalt
open RevHalt.Trilemma
open RevHalt.Instances

#print axioms RevHalt.frontier_nonempty_of_route_II

-- Search for Constructive Bridge
#find _ (PA_at (Provable := ?P) (K := ?K) (Machine := ?M) (encode_halt := ?E)
  (Cn := ?C) (A0 := ?A0) (hIdem := ?I) (hProvCn := ?PC) ?PA ?t →
  RouteIIAt (Provable := ?P) (K := ?K) (Machine := ?M) (encode_halt := ?E)
    (omegaΓ (Provable := ?P) (K := ?K) (Machine := ?M) (encode_halt := ?E)
      (Cn := ?C) (hIdem := ?I) (hProvCn := ?PC)
      (chainState (Provable := ?P) (K := ?K) (Machine := ?M) (encode_halt := ?E)
        (Cn := ?C) (A0 := ?A0) (hIdem := ?I) (hProvCn := ?PC) ?t)))

-- Search for CofinalWitness (constructive)
-- Note: CofinalWitness is Type, so we search for terms of that Type.
#find _ (CofinalWitness (PairPA (Provable := ?P) (K := ?K) (Machine := ?M)
  (encode_halt := ?E) (Cn := ?C) (A0 := ?A0)
  (hIdem := ?I) (hProvCn := ?PC) ?PA ?mode))
