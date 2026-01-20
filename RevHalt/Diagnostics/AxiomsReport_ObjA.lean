import RevHalt.Theory.Instances.TSP_ProofComplexity
import RevHalt.Theory.Instances.ThreeSAT_ProofComplexity
import RevHalt.Theory.ProofComplexity.Correspondence

namespace RevHalt.Diagnostics

/-!
Objective A axiom drilldown.

This file is a diagnostic only. It is not imported by the main development.

Run:
  `lake env lean RevHalt/Diagnostics/AxiomsReport_ObjA.lean`
-/

-- Proof complexity core
#print axioms RevHalt.ProofComplexity.toPPS
#print axioms RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS
#print axioms RevHalt.ProofComplexity.PolyPPS_implies_PolyPosWC

-- TSP instantiation
#print axioms RevHalt.TSP.IsTrue_TSP_of_ChecksWC
#print axioms RevHalt.TSP.ChecksWC_complete_of_PolyPosWC_TSP
#print axioms RevHalt.TSP.TSP_PPS
#print axioms RevHalt.TSP.PolyPosWC_TSP_implies_PolyPPS
#print axioms RevHalt.TSP.PolyPosWC_TSP_of_Stable_of_decidable
#print axioms RevHalt.TSP.PosCompleteWC_of_S1Rel_empty_TSP_of_decidable
#print axioms RevHalt.TSP.PolyCompressionWC_TSP_of_Stable_of_decidable_implies_PolyPPS

-- 3SAT instantiation
#print axioms RevHalt.ThreeSATCanonization.IsTrue_3SAT_of_ChecksWC
#print axioms RevHalt.ThreeSATCanonization.ChecksWC_complete_of_PolyPosWC_3SAT
#print axioms RevHalt.ThreeSATCanonization.SAT_PPS
#print axioms RevHalt.ThreeSATCanonization.PolyPosWC_3SAT_implies_PolyPPS
#print axioms RevHalt.ThreeSATCanonization.PosCompleteWC_of_S1Rel_empty_3SAT
#print axioms RevHalt.ThreeSATCanonization.PolyPosWC_3SAT_of_Stable_of_decidable
#print axioms RevHalt.ThreeSATCanonization.PolyCompressionWC_3SAT_of_Stable_of_decidable_implies_PolyPPS

-- Drilldown: where does Classical.choice enter?
#print axioms RevHalt.TSP.decodeList
#print axioms RevHalt.TSP.decodeTSP
#print axioms RevHalt.TSP.checkTour
#print axioms RevHalt.TSP.checkTour_sound
#print axioms RevHalt.TSP.ChecksWitness_TSP
#print axioms RevHalt.TSP.decodeListAux
#print axioms RevHalt.TSP.right_lt_pair_of_left_pos
#print axioms RevHalt.TSP.Machine_TSP_halts_iff

-- Mathlib/Cantor pairing facts used for termination
#print axioms Nat.pair_unpair
#print axioms Nat.right_le_pair
#print axioms Nat.unpair_right_le
#print axioms Nat.unpair_pair
#print axioms Nat.unpair
#print axioms Nat.pair

end RevHalt.Diagnostics
