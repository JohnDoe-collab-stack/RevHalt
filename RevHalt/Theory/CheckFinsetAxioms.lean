import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

-- Checked used lemmas
#print axioms Finset.sum_insert
#print axioms Finset.insert_erase
#print axioms Finset.notMem_erase
#print axioms Finset.sum_eq_zero
#print axioms Finset.mem_of_mem_erase
#print axioms Finset.ne_of_mem_erase

-- Check alternative approaches
#print axioms Finset.filter
#print axioms Finset.sum_filter
#print axioms Finset.sum_add_sum_compl
