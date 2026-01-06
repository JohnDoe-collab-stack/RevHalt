import RevHalt.Theory.Arithmetization.EvalnGraph0

open RevHalt
open RevHalt.Arithmetic
open RevHalt.Arithmetic.Pure
open FirstOrder
open scoped FirstOrder

namespace Scratch

private def fin0Val : Fin 0 → ℕ := fun i => Fin.elim0 i

-- Attempt to get a usable elimination lemma for AllNodesOK
theorem allNodesOK_elim (D r i : ℕ) (h : AllNodesOK.Realize ![D,r]) (hi : i ≤ r) : True := by
  have hBF : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) AllNodesOK ![D,r] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := AllNodesOK) (x := ![D,r])
      (y := (default : Fin 0 → ℕ))).2 h
  have hForall : ∀ x : ℕ,
      ((bdLe (α := Fin 2) (n := 1)
              (FirstOrder.Language.Term.var (Sum.inr (0 : Fin 1)))
              (FirstOrder.Language.Term.var (Sum.inl (1 : Fin 2)))).Realize ![D,r]
          (Fin.snoc (default : Fin 0 → ℕ) x) →
        ((show Lang0.BoundedFormula (Fin 2) 0 from NodeOK).relabel (![Sum.inl 0, Sum.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1)).Realize
          ![D,r] (Fin.snoc (default : Fin 0 → ℕ) x)) := by
    -- try simp
    simpa [AllNodesOK, FirstOrder.Language.Formula.Realize] using hBF
  have hAnte : (bdLe (α := Fin 2) (n := 1)
          (FirstOrder.Language.Term.var (Sum.inr (0 : Fin 1)))
          (FirstOrder.Language.Term.var (Sum.inl (1 : Fin 2)))).Realize ![D,r] (Fin.snoc (default : Fin 0 → ℕ) i) := by
    -- use bdLe_realize
    --
    --
    --
    admit
  have := hForall i hAnte
  trivial

end Scratch
