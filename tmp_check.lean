import Mathlib
example (z : Complex) : 2 * (z * (starRingEnd Complex) (-z)).re = - (2 * Complex.normSq z) := by
  simp [Complex.normSq]
  ring
