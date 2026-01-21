import RevHalt.Theory.Instances.TSP_ProofComplexity
import RevHalt.Theory.Instances.ThreeSAT_ProofComplexity
import RevHalt.Theory.ProofComplexity.Correspondence
import RevHalt.Theory.ProofComplexity.Simulation

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
-- Robustness core: simulation => transfer of p-boundedness
#print axioms RevHalt.ProofComplexity.PPSSimulates
#print axioms RevHalt.ProofComplexity.PolynomiallyBoundedPPS_of_simulation

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

-- Drilldown: confirm `Classical.choice` does not leak into Objective A endpoints.
-- (It still appears in Mathlib's Cantor pairing facts `Nat.unpair_pair`, etc.)
#print axioms RevHalt.TSP.decodeList
#print axioms RevHalt.TSP.decodeTSP
#print axioms RevHalt.TSP.checkTour
#print axioms RevHalt.TSP.checkTour_sound
#print axioms RevHalt.TSP.ChecksWitness_TSP
#print axioms RevHalt.TSP.decodeListAux
#print axioms RevHalt.TSP.right_lt_pair_of_left_pos
#print axioms RevHalt.TSP.Machine_TSP_halts_iff

-- 3SAT drilldown
#print axioms RevHalt.ThreeSAT.encodeList
#print axioms RevHalt.ThreeSAT.decodeList
#print axioms RevHalt.ThreeSAT.pair
#print axioms RevHalt.ThreeSAT.unpairAux
#print axioms RevHalt.ThreeSAT.unpair
#print axioms RevHalt.ThreeSAT.pair_ne_zero
#print axioms RevHalt.ThreeSAT.le_pow_two
#print axioms RevHalt.ThreeSAT.unpairAux_pair
#print axioms RevHalt.ThreeSAT.unpair_pair
#print axioms RevHalt.ThreeSAT.unpair_fst_pair
#print axioms RevHalt.ThreeSAT.unpair_snd_pair
#print axioms RevHalt.ThreeSAT.decodeListAux_encodeList
#print axioms RevHalt.ThreeSAT.decodeList_encodeList
#print axioms RevHalt.ThreeSAT.decode3SAT
#print axioms RevHalt.ThreeSAT.satWitness
#print axioms RevHalt.ThreeSAT.Machine_3SAT_halts_iff

-- Mathlib/Cantor pairing facts used for termination
#print axioms Nat.pair_unpair
#print axioms Nat.right_le_pair
#print axioms Nat.unpair_right_le
#print axioms Nat.unpair_pair
#print axioms Nat.unpair
#print axioms Nat.pair

-- Spot-check: do core Nat lemmas already use Classical.choice?
#print axioms Nat.le_mul_of_pos_right
#print axioms Nat.mul_div_right
#print axioms Nat.div_eq_of_lt
#print axioms Nat.one_le_pow
#print axioms Nat.succ_ne_zero
#print axioms Nat.succ_pos
#print axioms Nat.not_succ_le_zero
#print axioms Nat.succ_le_succ_iff
#print axioms Nat.succ_le_iff
#print axioms Nat.succ_le_succ
#print axioms Nat.add_sub_cancel
#print axioms Nat.sub_add_cancel
#print axioms Nat.succ_sub_one
#print axioms pow_pos
#print axioms Prod.ext

end RevHalt.Diagnostics
