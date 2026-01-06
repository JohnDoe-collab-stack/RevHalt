import RevHalt.Theory.Arithmetization.EvalnGraph0

open RevHalt
open RevHalt.Arithmetic
open RevHalt.Arithmetic.Pure
open FirstOrder
open scoped FirstOrder

namespace Scratch

theorem test (D r : ℕ) (h : AllNodesOK.Realize ![D,r]) : True := by
  -- Unfolding attempt
  have h' := h
  -- simp should unfold `Realize` for quantifier and implication.
  -- We don't use the result; just ensure it elaborates.
  -- Note: `simp` creates goals; we avoid using it directly.
  have : (∀ i : ℕ, i ≤ r → True) := by
    intro i hi
    trivial
  trivial

end Scratch
