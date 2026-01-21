import RevHalt.Theory.ProofComplexity.Simulation

namespace RevHalt.Diagnostics

/-!
Simulation axiom drilldown.

This file is a diagnostic only. It is not imported by the main development.

Run:
  `lake env lean RevHalt/Diagnostics/AxiomsReport_Simulation.lean`
-/

#print axioms RevHalt.Complexity.IsPoly.mul_const
#print axioms RevHalt.Complexity.IsPoly.add_const
#print axioms RevHalt.Complexity.IsPoly.pow_const
#print axioms RevHalt.Complexity.IsPoly.comp

#print axioms RevHalt.ProofComplexity.PPSSimulates
#print axioms RevHalt.ProofComplexity.PolynomiallyBoundedPPS_of_simulation

end RevHalt.Diagnostics

