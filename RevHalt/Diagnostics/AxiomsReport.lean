import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_TwoSided
import RevHalt.Theory.TheoryDynamics_Transfinite
import RevHalt.Theory.Instances.TSP_Dynamics
import RevHalt.Theory.Instances.TSP_Canonization

namespace RevHalt.Diagnostics

/-!
This file is a diagnostic: it prints (via `#print axioms`) which axioms a selection
of key theorems depends on. It is not imported by the main development.

Run:
  `lake env lean RevHalt/Diagnostics/AxiomsReport.lean`
-/

-- Trilemma: constructive "not-all" vs classical "disjunction" form
#print axioms RevHalt.omega_trilemma_not_all
#print axioms RevHalt.omega_trilemma_disjunction

-- Two-sided dynamics: monotonicity with/without decidability
#print axioms RevHalt.F0_pm_monotone_of_provClosed
#print axioms RevHalt.F0_pm_monotone_classical

-- Transfinite: continuity -> fixpoint at a limit ordinal
#print axioms RevHalt.continuous_implies_fixpoint_at_limit

-- TSP instance: stability at omega, and the collapse endpoint
#print axioms RevHalt.TSP.S1Rel_empty_at_omega_of_absorbable_and_admissible
#print axioms RevHalt.TSP.Collapse_TSP_of_TrajectoryChoice_and_PriceOfP

end RevHalt.Diagnostics
