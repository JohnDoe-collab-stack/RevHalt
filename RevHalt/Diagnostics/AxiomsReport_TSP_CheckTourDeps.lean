import RevHalt.Theory.Instances.TSP

namespace RevHalt.Diagnostics

/-!
Diagnostics for the remaining `Quot.sound` dependency in `RevHalt.TSP.checkTour`.

Run:
  `lake env lean RevHalt/Diagnostics/AxiomsReport_TSP_CheckTourDeps.lean`
-/

#print axioms RevHalt.TSP.checkTour
#print axioms RevHalt.TSP.all_lt_of_all_eq_true
#print axioms RevHalt.TSP.tourCost

-- Suspects used inside `checkTour`.
#print axioms List.all_eq_true
#print axioms decide_eq_true_iff
#print axioms Bool.and_eq_true
#print axioms List.get
#print axioms List.Nodup

end RevHalt.Diagnostics
