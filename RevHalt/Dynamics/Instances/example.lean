import RevHalt.Dynamics.Core.Fork

namespace Example

open RevHalt
open RevHalt.Dynamics.Core

variable {Code PropT : Type}
variable (ctx : EnrichedContext Code PropT)
variable (T0 : TheoryNode ctx)
variable (p : PropT)

-- A certificate that the pivot is true (comes from your verifier/oracle layer)
variable (hp : ctx.Truth p)

-- Build the fork object (no global choice)
def F : Fork ctx T0 := Fork.ofPivot ctx T0 p

-- Materialize the left branch (requires the certificate)
def T_left : TheoryNode ctx := (F ctx T0 p).left hp

-- It is reachable in one step (edge / path integration already proved in your file)
theorem edge_to_left : Edge ctx T0 ((Fork.ofPivot ctx T0 p).left hp) :=
  Fork.ofPivot_edge_left ctx T0 p hp

-- And the fork encodes the impossibility of both sound extensions
theorem not_both_sound :
  ¬ (TheorySound ctx (Extend T0.theory p) ∧
     TheorySound ctx (Extend T0.theory (ctx.Not p))) :=
  (Fork.ofPivot ctx T0 p).exclusion

end Example
