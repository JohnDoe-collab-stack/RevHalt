import RevHalt.Theory.Arithmetization.EvalnGraph0

namespace RevHalt.Arithmetic.Pure

open FirstOrder
open scoped FirstOrder

example (D i : ℕ) (h : NodeOK.Realize ![D,i]) : True := by
  have h0 : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) NodeOK ![D,i] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := NodeOK) (x := ![D,i]) (y := (default : Fin 0 → ℕ))).1 h
  rcases (by simpa [NodeOK] using h0) with ⟨k, code, input, output, c1, c2, kpred, hk⟩
  rcases hk with ⟨hNodeStage, hCase⟩
  rcases hNodeStage with ⟨hNodeAt, hStage⟩
  -- Try to simp stage
  have hkSucc : k = Nat.succ kpred := by
    -- stageOK is a conjunction
    have : (FirstOrder.Language.Term.bdEqual (FirstOrder.Language.Term.var (Sum.inr 0)) (succTerm (FirstOrder.Language.Term.var (Sum.inr 6)))).Realize
      (![D,i] : Fin 2 → ℕ) (![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ) := by
      -- not accessible
      admit
  trivial

end RevHalt.Arithmetic.Pure
