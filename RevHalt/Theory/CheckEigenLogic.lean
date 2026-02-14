import RevHalt.Theory.PrimitiveHolonomy_Unitarity

theorem test_eigen_logic_manual {R : Type} [CommRing R] [IsDomain R] [DecidableEq R]
    (a b : R) (hNZ : b ≠ 0) (hProd : a * b = 0) : a = 0 := by
  have hOr := eq_zero_or_eq_zero_of_mul_eq_zero hProd
  cases hOr with
  | inl hA => exact hA
  | inr hB => contradiction

#print axioms test_eigen_logic_manual
