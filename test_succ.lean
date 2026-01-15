import Mathlib.SetTheory.Ordinal.Arithmetic
#check @Order.succ
example (γ : Ordinal) : Order.succ γ = γ + 1 := Order.succ_eq_succ γ
