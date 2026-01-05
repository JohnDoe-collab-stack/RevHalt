import RevHalt.Theory.Arithmetization.NatPair0
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.NatUnpair0

Pure-arithmetic utilities for working with `Nat.unpair` **without** arithmetizing `sqrt`.

We never define `unpair` directly in the pure language `Lang0`. Instead, we use witnesses
`a b` such that `Nat.pair a b = n` (via `pairGraph`) and then rewrite with
`Nat.unpair_pair` / `Nat.pair_unpair` in the meta-theory.

This file packages two common derived relations as pure formulas:

- `unpair1Graph(n,a)`  ↔  `n.unpair.1 = a`
- `unpair2Graph(n,b)`  ↔  `n.unpair.2 = b`

These are small convenience bricks for the full arithmetization of `evaln`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

private def nVar : Lang0.Term (Fin 2 ⊕ Fin 1) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

private def aVar : Lang0.Term (Fin 2 ⊕ Fin 1) :=
  FirstOrder.Language.Term.var (Sum.inl 1)

private def bVar : Lang0.Term (Fin 2 ⊕ Fin 1) :=
  FirstOrder.Language.Term.var (Sum.inr 0)

private def pairRelabel1 : Fin 3 → Fin 2 ⊕ Fin 1 :=
  ![Sum.inl 1, Sum.inr 0, Sum.inl 0]

private def pairRelabel2 : Fin 3 → Fin 2 ⊕ Fin 1 :=
  ![Sum.inr 0, Sum.inl 1, Sum.inl 0]

/--
`unpair1Graph(n,a)` holds iff `∃ b, Nat.pair a b = n`.

In the standard model this is equivalent to `n.unpair.1 = a`.
-/
def unpair1Graph : Lang0.Formula (Fin 2) :=
  ∃' (show Lang0.BoundedFormula (Fin 2) 1 from
    (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairRelabel1)

/--
`unpair2Graph(n,b)` holds iff `∃ a, Nat.pair a b = n`.

In the standard model this is equivalent to `n.unpair.2 = b`.
-/
def unpair2Graph : Lang0.Formula (Fin 2) :=
  ∃' (show Lang0.BoundedFormula (Fin 2) 1 from
    (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairRelabel2)

theorem unpair1Graph_realize (n a : ℕ) :
    unpair1Graph.Realize ![n, a] ↔ n.unpair.1 = a := by
  -- Switch to `BoundedFormula.Realize` to unfold `∃'` using simp.
  have h0 :
      unpair1Graph.Realize ![n, a] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair1Graph ![n, a]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := unpair1Graph) (x := ![n, a])
          (y := (default : Fin 0 → ℕ))).symm

  have hSnoc0 {p : Fin 0 → ℕ} {b : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p b 0 = b := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := b) (p := p) (n := 0))

  -- Compute the relabelled valuation as `![a, b, n]`.
  have hPairVal (b : ℕ) :
      (Sum.elim (![n, a] : Fin 2 → ℕ) (![b] : Fin 1 → ℕ) ∘ pairRelabel1) = ![a, b, n] := by
    funext j
    fin_cases j <;> simp [pairRelabel1]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair1Graph ![n, a]
          (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [unpair1Graph] using h') with ⟨b, hb⟩
    have hb' : pairGraph.Realize ![a, b, n] := by
      have : pairGraph.Realize (Sum.elim (![n, a] : Fin 2 → ℕ) (![b] : Fin 1 → ℕ) ∘ pairRelabel1) := by
        simpa [hSnoc0, hPairVal b] using hb
      simpa [hPairVal b] using this
    have hPair : Nat.pair a b = n := (pairGraph_realize a b n).1 hb'
    -- Convert `Nat.pair a b = n` into `n.unpair.1 = a`.
    have : n.unpair = (a, b) := by
      simpa [hPair] using (Nat.unpair_pair a b)
    simp [this]
  · intro h
    -- Use `b := n.unpair.2` and `Nat.pair_unpair` to witness the existential.
    have hPair : Nat.pair (n.unpair.1) (n.unpair.2) = n := by
      simp
    have hPair' : Nat.pair a (n.unpair.2) = n := by simpa [h] using hPair
    have hb : pairGraph.Realize ![a, n.unpair.2, n] := (pairGraph_realize a (n.unpair.2) n).2 hPair'
    have hb' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair1Graph ![n, a]
          (default : Fin 0 → ℕ) := by
      simp [unpair1Graph]
      refine ⟨n.unpair.2, ?_⟩
      -- Reduce the relabeling.
      have : pairGraph.Realize (Sum.elim (![n, a] : Fin 2 → ℕ) (![n.unpair.2] : Fin 1 → ℕ) ∘ pairRelabel1) := by
        simpa [hPairVal (n.unpair.2)] using hb
      simpa [hPairVal (n.unpair.2)] using this
    exact (h0).2 hb'

theorem unpair2Graph_realize (n b : ℕ) :
    unpair2Graph.Realize ![n, b] ↔ n.unpair.2 = b := by
  have h0 :
      unpair2Graph.Realize ![n, b] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair2Graph ![n, b]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := unpair2Graph) (x := ![n, b])
          (y := (default : Fin 0 → ℕ))).symm

  have hSnoc0 {p : Fin 0 → ℕ} {a : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p a 0 = a := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := a) (p := p) (n := 0))

  have hPairVal (a : ℕ) :
      (Sum.elim (![n, b] : Fin 2 → ℕ) (![a] : Fin 1 → ℕ) ∘ pairRelabel2) = ![a, b, n] := by
    funext j
    fin_cases j <;> simp [pairRelabel2]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair2Graph ![n, b]
          (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [unpair2Graph] using h') with ⟨a, ha⟩
    have ha' : pairGraph.Realize ![a, b, n] := by
      have : pairGraph.Realize (Sum.elim (![n, b] : Fin 2 → ℕ) (![a] : Fin 1 → ℕ) ∘ pairRelabel2) := by
        simpa [hSnoc0, hPairVal a] using ha
      simpa [hPairVal a] using this
    have hPair : Nat.pair a b = n := (pairGraph_realize a b n).1 ha'
    have : n.unpair = (a, b) := by
      simpa [hPair] using (Nat.unpair_pair a b)
    simp [this]
  · intro h
    have hPair : Nat.pair (n.unpair.1) (n.unpair.2) = n := by
      simp
    have hPair' : Nat.pair (n.unpair.1) b = n := by simpa [h] using hPair
    have ha : pairGraph.Realize ![n.unpair.1, b, n] :=
      (pairGraph_realize (n.unpair.1) b n).2 hPair'
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) unpair2Graph ![n, b]
          (default : Fin 0 → ℕ) := by
      simp [unpair2Graph]
      refine ⟨n.unpair.1, ?_⟩
      have : pairGraph.Realize (Sum.elim (![n, b] : Fin 2 → ℕ) (![n.unpair.1] : Fin 1 → ℕ) ∘ pairRelabel2) := by
        simpa [hPairVal (n.unpair.1)] using ha
      simpa [hPairVal (n.unpair.1)] using this
    exact (h0).2 h'

end Pure

end Arithmetic

end RevHalt
