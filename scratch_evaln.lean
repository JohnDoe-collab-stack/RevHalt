import Mathlib.Computability.PartrecCode

open Nat.Partrec

namespace Scratch

example (kpred input : ℕ) (h : input ≤ kpred) :
    Code.evaln (kpred + 1) Code.zero input = some 0 := by
  -- see simp
  simp [Code.evaln, h]

example (kpred input : ℕ) (h : input ≤ kpred) :
    Code.evaln (kpred + 1) Code.succ input = some (Nat.succ input) := by
  simp [Code.evaln, h]

end Scratch
