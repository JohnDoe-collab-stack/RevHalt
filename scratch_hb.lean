import Mathlib.Data.Nat.Basic

example (n : Nat) : True := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    trivial
