import RevHalt.Theory.ProofComplexity.Simulation
import RevHalt.Theory.TheoryDynamics_ComplexityBounds

namespace RevHalt.Diagnostics

/-!
Fine-grained axiom drilldown for the Objective A bridge.

Run:
  `lake env lean RevHalt/Diagnostics/AxiomsReport_IsPolyCompDetail.lean`
-/

#print axioms RevHalt.Complexity.IsPoly
#print axioms RevHalt.Complexity.pow_succ_le_two_pow_mul_add_one

#print axioms Nat.pow_le_pow_left
#print axioms Nat.one_le_pow
#print axioms Nat.le_mul_of_pos_right
#print axioms Nat.mul_le_mul_left
#print axioms Nat.mul_le_mul_right
#print axioms Nat.add_le_add_left
#print axioms Nat.add_le_add_right
#print axioms Nat.succ_pos
#print axioms Nat.pos_of_ne_zero
#print axioms Nat.succ_le_iff
#print axioms Nat.le_add_right
#print axioms Nat.le_add_left
#print axioms Nat.add_lt_add_left
#print axioms lt_of_le_of_ne
#print axioms Nat.two_mul
#print axioms Nat.mul_add
#print axioms Nat.add_mul
#print axioms Nat.pow_succ
#print axioms Nat.mul_comm
#print axioms Nat.mul_left_comm
#print axioms Nat.mul_assoc
#print axioms Nat.add_comm
#print axioms Nat.add_left_comm
#print axioms Nat.add_assoc
#print axioms Nat.instMonoid
#print axioms Monoid.toNatPow
#print axioms instLENat
#print axioms instAddNat
#print axioms instMulNat
#print axioms instHAdd
#print axioms instHMul
#print axioms instHPow
#print axioms Nat.mul_pow
#print axioms Nat.pow_mul

#print axioms RevHalt.Complexity.IsPoly.comp

end RevHalt.Diagnostics
