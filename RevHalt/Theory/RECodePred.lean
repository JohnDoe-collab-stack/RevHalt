import Mathlib.Computability.PartrecCode

/-!
# RevHalt.Theory.RECodePred

RevHalt often needs the same r.e./semi-decidability interface over `Nat.Partrec.Code`:

`P : Code → Prop` is semi-decidable if there exists a partial recursive `f` such that
`P c` holds exactly when `f c 0` converges.

We package that pattern as a small reusable structure.
-/

namespace RevHalt

open Nat.Partrec

/-- A semi-decidable predicate on `Code`, witnessed by a partial recursive semi-decider. -/
structure RECodePred (P : Code → Prop) where
  /-- The semi-decider (halts iff `P c`). -/
  f : Code → (Nat →. Nat)
  /-- `f` is partial recursive in `(c, n)`. -/
  f_partrec : Partrec₂ f
  /-- Specification: `P c` iff the semi-decider converges at input `0`. -/
  spec : ∀ c, P c ↔ (∃ x : Nat, x ∈ (f c) 0)

end RevHalt

