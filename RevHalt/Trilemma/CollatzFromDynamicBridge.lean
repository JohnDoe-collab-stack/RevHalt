/-
  CollatzFromDynamicBridge.lean

  Glue: build a `Generic.CollatzInstance` using the *dynamic* bridge (no universal machine),
  then derive the standard Collatz conclusion already proved in `CollatzDynamicPA.lean`.
-/

import RevHalt.Trilemma.CollatzDynamicPA
import RevHalt.Instances.ConcreteBridgeDynamicMin

namespace RevHalt.Trilemma

open RevHalt.Instances

/-- Collatz (for positive seeds) from a dynamic-bridge instance package. -/
theorem collatz_conjecture_of_dynamic_bridge
    (D : ConcreteBridgeDynamicAssumptionsD) :
    ∀ seed : Nat, ∃ n, Collatz.iter n (seed + 1) = 1 := by
  -- Build the instance and apply the already-proved theorem.
  exact App.collatz_conjecture_of_instance (I := ConcreteInstance_of_dynamic_D D)

end RevHalt.Trilemma

