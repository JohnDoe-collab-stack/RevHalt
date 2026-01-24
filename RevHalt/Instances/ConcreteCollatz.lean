/-
  ConcreteCollatz.lean

  Phase 2 skeleton:
  - Builds a `Generic.CollatzInstance` as a single bundled value.
  - For now, it uses the placeholder axioms from `CollatzWitnesses` and `CollatzBridge`.
  - Later: replace these axioms with actual constructions/proofs, and the bundle stays unchanged.
-/

import RevHalt.Trilemma.GenericExtinction
import RevHalt.Instances.CollatzWitnesses
import RevHalt.Instances.CollatzBridge

namespace RevHalt.Instances

open RevHalt.Trilemma.Generic

/-
  Missing structural fields for `CollatzInstance`:

  Your current `CollatzWitnesses.lean` provides:
    PropT Code Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn witBC witAC witAB

  But `CollatzInstance` also requires:
    hMono : ProvRelMonotone Provable
    hCnExt : CnExtensive Cn

  For the skeleton, we declare them as axioms here.
  In Phase 2 completion, replace these axioms by actual proofs (or move them into
  CollatzWitnesses if you prefer a single “axiom surface” file).
-/


/-- The bundled concrete instance (currently placeholder-based). -/
def ConcreteInstance : CollatzInstance :=
{ PropT      := PropT
  Code       := Code
  Provable   := Provable
  K          := K
  Machine    := Machine
  encode_halt := encode_halt
  Cn         := Cn
  A0         := A0
  PAax       := PAax

  hIdem      := hIdem
  hProvCn    := hProvCn
  hMono      := hMono
  hCnExt     := hCnExt

  witBC      := witBC
  witAC      := witAC
  witAB      := witAB

  bridge     := bridge_proof
}

#print axioms ConcreteInstance

end RevHalt.Instances
