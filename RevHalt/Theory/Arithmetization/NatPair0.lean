import RevHalt.Theory.Arithmetization.BasicNat0
import Mathlib.Data.Nat.Pairing

/-!
# RevHalt.Theory.Arithmetization.NatPair0

Pure-arithmetic definability of the **graph** of `Nat.pair`.

This is a useful brick for the “full arithmetization” track:

- `Nat.Partrec.Code.evaln` uses `Nat.pair`/`Nat.unpair` as its data encoding.
- In the pure language `Lang0` we do not have `pair` as a function symbol, but we can still
  *define its graph* as a formula using only `<`, `+`, `*`, and `=`.

We do **not** attempt to arithmetize `Nat.unpair` directly (it uses `sqrt` in its definition).
Instead, whenever a proof needs “`n.unpair = (a,b)`”, we can use witnesses `a b` together with the
constraint `Nat.pair a b = n`, which is what `unpair_pair` gives in the standard model.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

private def v0 : Lang0.Term (Fin 3 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

private def v1 : Lang0.Term (Fin 3 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 1)

private def v2 : Lang0.Term (Fin 3 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 2)

/--
`pairGraph` is the pure arithmetic formula on three free variables:

`pairGraph(x,y,z)` ↔ `Nat.pair x y = z`.
-/
def pairGraph : Lang0.Formula (Fin 3) :=
  let x := v0
  let y := v1
  let z := v2
  let xyLt : Lang0.Formula (Fin 3) := (bdLt x y)
  let zEqLt : Lang0.Formula (Fin 3) :=
    FirstOrder.Language.Term.bdEqual z (addTerm (mulTerm y y) x)
  let zEqGe : Lang0.Formula (Fin 3) :=
    FirstOrder.Language.Term.bdEqual z (addTerm (addTerm (mulTerm x x) x) y)
  (xyLt ⊓ zEqLt) ⊔ (xyLt.not ⊓ zEqGe)

theorem pairGraph_realize (a b c : ℕ) :
    pairGraph.Realize ![a, b, c] ↔ Nat.pair a b = c := by
  -- Switch to `BoundedFormula.Realize` (0 bound variables) to use the generic `bdLt_realize` lemma.
  have h0 :
      pairGraph.Realize ![a, b, c] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairGraph ![a, b, c]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := pairGraph) (x := ![a, b, c])
          (y := (default : Fin 0 → ℕ))).symm

  -- Evaluate the pure formula in the standard model.
  have hEval :
      FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairGraph ![a, b, c] (default : Fin 0 → ℕ) ↔
        Nat.pair a b = c := by
    by_cases h : a < b
    · have hEq : Nat.pair a b = b * b + a := by simp [Nat.pair, h]
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairGraph ![a, b, c] (default : Fin 0 → ℕ) ↔
          c = b * b + a := by
        simp [pairGraph, h, v0, v1, v2, addTerm, mulTerm]
      constructor
      · intro hc
        have hc' : c = b * b + a := this.1 hc
        simp [hEq, hc']
      · intro hc
        have hEqC : b * b + a = c := by
          simpa [hEq] using hc
        have hc' : c = b * b + a := hEqC.symm
        exact this.2 hc'
    · have hEq : Nat.pair a b = a * a + a + b := by simp [Nat.pair, h]
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairGraph ![a, b, c] (default : Fin 0 → ℕ) ↔
          c = a * a + a + b := by
        simp [pairGraph, h, v0, v1, v2, addTerm, mulTerm]
      constructor
      · intro hc
        have hc' : c = a * a + a + b := this.1 hc
        simp [hEq, hc']
      · intro hc
        have hEqC : a * a + a + b = c := by
          simpa [hEq] using hc
        have hc' : c = a * a + a + b := hEqC.symm
        exact this.2 hc'

  exact h0.trans hEval

end Pure

end Arithmetic

end RevHalt
