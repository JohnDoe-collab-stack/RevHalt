/-
  CollatzBridge.lean

  Isolation of the Consistency Bridge proof.
  Goal: Prove `PA_implies_RouteIIAt`.

  Implementation:
  Applies the Generic Route II theorem (`frontier_nonempty_of_route_II`).
  Requires proving Soundness, NegativeCompleteness, and Barrier
  for the specific `Provable` and `Machine`.
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Instances.CollatzWitnesses
import RevHalt.Trilemma.CofinalHornsPA

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic
open RevHalt.Trilemma -- For PA_in

lemma bridge_proof : PA_implies_RouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) (PAax := PAax) := by
  intro t hPAt

  -- 1) Promote PA_at t to PA_in omegaΓ
  -- PA_at t says PA ⊆ Γ_t. Because Γ_t ⊆ ωΓ, we have PA ⊆ ωΓ.
  have hPAω :
      PA_in (PropT := PropT) (PAax := PAax)
        (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
          (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t))
      := by
    intro p hp
    -- Proof: p ∈ PA → p ∈ Γ_t.
    -- Γ_t is the 0-th element of the chain starting at Γ_t.
    refine ⟨0, ?_⟩
    exact hPAt hp

  -- 2) Deduce RouteIIAt (Frontier Nonempty) from PA_in
  -- This step requires the system to satisfy the "Barrier" (Route II)
  -- effectively claiming that if PA is in the limit theory, the frontier cannot be empty.
  -- This lemma would be `RouteIIAt_of_PA_in_omega`.
  exact (sorry : PA_in _ _ → _) hPAω

#print axioms bridge_proof

end RevHalt.Instances
