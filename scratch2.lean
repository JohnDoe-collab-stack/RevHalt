import RevHalt.Theory.Arithmetization.EvalnGraph0

open RevHalt
open RevHalt.Arithmetic
open RevHalt.Arithmetic.Pure
open FirstOrder
open scoped FirstOrder

namespace Scratch

-- Try unfolding AllNodesOK.Realize.
theorem test (D r : ℕ) (h : AllNodesOK.Realize ![D,r]) : True := by
  -- see if simp can unfold
  have h' := h
  -- The following line is just to check it elaborates; it won't run.
  -- We'll rewrite h' and then close with trivial.
  trivial

end Scratch
