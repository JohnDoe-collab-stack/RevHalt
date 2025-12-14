/-!
# RevHalt.Instances

Entry point for Instance modules (PA, Mathlib PRModel).

These instances provide concrete implementations of the RevHalt framework
for specific theories (Peano Arithmetic) and computability models (Mathlib Partrec).
-/

-- PA Instance
import RevHalt.Instances.PA

-- Mathlib-based PRModel
import RevHalt.Instances.Arithmetization
