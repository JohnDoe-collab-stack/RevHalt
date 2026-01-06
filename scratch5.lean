import RevHalt.Theory.Arithmetization.EvalnGraph0

open RevHalt
open RevHalt.Arithmetic.Pure
open FirstOrder
open scoped FirstOrder

namespace Scratch

-- Try to prove the antecedent lemma by simp.
example (D r i : ℕ) (hi : i ≤ r) :
    (bdLe (α := Fin 2) (n := 1)
          (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)).Realize
      (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i) := by
  -- Use bdLe_realize
  have : (bvar (α := Fin 2) (n := 1) 0).realize
        (Sum.elim (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i)) ≤
      (termVar (α := Fin 2) (n := 1) 1).realize
        (Sum.elim (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i)) := by
    -- simp should make this exactly hi
    simpa [bvar, termVar] using hi
  exact (bdLe_realize (α := Fin 2) (n := 1)
      (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)
      (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i)).2 this

end Scratch
