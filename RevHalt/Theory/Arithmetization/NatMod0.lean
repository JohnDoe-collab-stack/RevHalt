import RevHalt.Theory.Arithmetization.BasicNat0
import Mathlib.Data.Nat.ModEq

/-!
# RevHalt.Theory.Arithmetization.NatMod0

Pure-arithmetic definability of the **division algorithm spec** (and hence `Nat.mod`) in `Lang0`.

For the “full arithmetization” track we frequently need to express statements of the form
`a % m = r` using only `0,succ,+,*` and `=`.

The standard route is to express the *graph* of remainder via a quotient witness:

`a % m = r`  (with `m > 0`)  iff  `∃ q, a = q*m + r ∧ r < m`.

This file implements the RHS as a pure arithmetic formula and proves the equivalence in `ℕ`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-!
### Term-level remainder witness (usable under extra binders)

`modGraphPos` is a plain formula on three free variables.
For arithmetization tasks we often want the same pattern applied to *terms* in an ambient context
that already has some bound variables. The helper `bdModPos` does exactly that.
-/

private def liftBoundVar {α : Type} {n : ℕ} : (α ⊕ Fin n) → (α ⊕ Fin (n + 1))
  | Sum.inl a => Sum.inl a
  | Sum.inr i => Sum.inr i.castSucc

private def liftBoundTerm {α : Type} {n : ℕ} (t : Lang0.Term (α ⊕ Fin n)) :
    Lang0.Term (α ⊕ Fin (n + 1)) :=
  t.relabel liftBoundVar

/-- Term-level version of `modGraphPos`: `∃ q, t = q*m + r ∧ r < m`. -/
def bdModPos {α : Type} {n : ℕ} (t m r : Lang0.Term (α ⊕ Fin n)) : Lang0.BoundedFormula α n :=
  ∃'
    let t' := liftBoundTerm (α := α) (n := n) t
    let m' := liftBoundTerm (α := α) (n := n) m
    let r' := liftBoundTerm (α := α) (n := n) r
    let q : Lang0.Term (α ⊕ Fin (n + 1)) :=
      FirstOrder.Language.Term.var (Sum.inr (Fin.last n))
    (FirstOrder.Language.Term.bdEqual t' (addTerm (mulTerm q m') r')) ⊓
      (bdLt (α := α) (n := n + 1) r' m')

/--
Semantics of the term-level remainder witness:

`bdModPos t m r` holds iff there exists a quotient `q` such that
`t = q*m + r` and `r < m` (evaluated in the standard model).
-/
theorem bdModPos_realize {α : Type} {n : ℕ} (t m r : Lang0.Term (α ⊕ Fin n))
    (v : α → ℕ) (xs : Fin n → ℕ) :
    (bdModPos (α := α) (n := n) t m r).Realize v xs ↔
      ∃ q : ℕ,
        t.realize (Sum.elim v xs) = q * m.realize (Sum.elim v xs) + r.realize (Sum.elim v xs) ∧
          r.realize (Sum.elim v xs) < m.realize (Sum.elim v xs) := by
  -- Unfold `bdModPos` and compute the effect of lifting on realizations.
  have hLift (q : ℕ) :
      (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) = Sum.elim v xs := by
    funext z
    cases z with
    | inl a => rfl
    | inr i =>
        simp [liftBoundVar, Fin.snoc_castSucc]
  constructor
  · intro h
    rcases (by
      simpa [bdModPos, addTerm, mulTerm, liftBoundTerm, liftBoundVar, succTerm] using h) with
        ⟨q, hEq, hLt⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [hLift q] using hEq
    · simpa [hLift q] using hLt
  · rintro ⟨q, hEq, hLt⟩
    -- Repackage the witness tuple back into `bdModPos`.
    have hEq' :
        t.realize (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) =
          q * m.realize (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) +
            r.realize (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) := by
      simpa [hLift q] using hEq
    have hLt' :
        r.realize (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) <
          m.realize (Sum.elim v (Fin.snoc xs q) ∘ liftBoundVar) := by
      simpa [hLift q] using hLt
    simpa [bdModPos, addTerm, mulTerm, liftBoundTerm, liftBoundVar, succTerm] using ⟨q, hEq', hLt'⟩

/--
`modGraphPos(a,m,r)` is the pure arithmetic formula expressing the division algorithm witness:

`∃ q, a = q*m + r ∧ r < m`.

This is the correct “graph of `mod`” when `m > 0`.
-/
def modGraphPos : Lang0.Formula (Fin 3) :=
  ∃'
    let a : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inl 0)
    let m : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inl 1)
    let r : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inl 2)
    let q : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inr 0)
    (FirstOrder.Language.Term.bdEqual a (addTerm (mulTerm q m) r)) ⊓ (bdLt r m)

theorem modGraphPos_realize (a m r : ℕ) :
    modGraphPos.Realize ![a, m, r] ↔ ∃ q, a = q * m + r ∧ r < m := by
  -- Switch to `BoundedFormula.Realize` (0 bound variables) to reuse the `[simp]` lemmas for `bdLt`.
  have h0 :
      modGraphPos.Realize ![a, m, r] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) modGraphPos ![a, m, r]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := modGraphPos) (x := ![a, m, r])
          (y := (default : Fin 0 → ℕ))).symm
  -- Evaluate in the standard model.
  -- After unfolding, `simp` turns `bdLt` into `<` via `bdLt_realize`.
  simpa [modGraphPos, addTerm, mulTerm] using h0

/--
Correctness of `modGraphPos` w.r.t. `Nat.mod`, for positive moduli.
-/
theorem modGraphPos_realize_iff_mod (a m r : ℕ) (hm : 0 < m) :
    modGraphPos.Realize ![a, m, r] ↔ a % m = r := by
  constructor
  · intro h
    rcases (modGraphPos_realize a m r).1 h with ⟨q, hEq, hrLt⟩
    -- From `a = q*m + r` we get `a ≡ r [MOD m]`, hence `a % m = r` because `r < m`.
    have hModEq : a ≡ r [MOD m] := by
      -- `ModEq` is definitional equality of mods.
      show a % m = r % m
      calc
        a % m = (q * m + r) % m := by simp [hEq]
        _ = (r + q * m) % m := by simp [Nat.add_comm]
        _ = r % m := by
          -- Reduce `(r + q*m) % m` to `r % m`.
          -- `Nat.add_mul_mod_self_left` is about `r + m*q`, so commute the product.
          simp [Nat.mul_comm]
    -- Now use the general lemma `mod_eq_of_modEq`.
    exact Nat.mod_eq_of_modEq hModEq hrLt
  · intro hMod
    -- Build witnesses from the quotient/remainder given by `Nat.div`/`Nat.mod`.
    have hrLt : r < m := by
      -- `r = a % m` and `a % m < m` when `m > 0`.
      simpa [hMod] using (Nat.mod_lt a hm)
    refine (modGraphPos_realize a m r).2 ?_
    refine ⟨a / m, ?_, hrLt⟩
    have hDivAdd : (a / m) * m + a % m = a := by
      -- `Nat.div_add_mod` gives `m * (a / m) + a % m = a`; commute the product.
      simpa [Nat.mul_comm] using (Nat.div_add_mod a m)
    -- Rewrite the remainder using `hMod`.
    exact (by simpa [hMod] using hDivAdd.symm)

end Pure

end Arithmetic

end RevHalt
