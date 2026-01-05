import RevHalt.Theory.Arithmetization.NatPair0
import RevHalt.Theory.Arithmetization.NatUnpair0
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.NatTuple0

Small pure-arithmetic helpers for *nested* `Nat.pair` encodings.

For the full arithmetization of `Nat.Partrec.Code.evaln`, it is convenient to encode larger
tuples using iterated pairing (e.g. `Nat.pair a (Nat.pair b c)`), and to have a reusable
formula-level graph for these encodings.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-! ### Triple pairing: `Nat.pair a (Nat.pair b c)` -/

private def pairBCRelabel : Fin 3 → Fin 4 ⊕ Fin 1 :=
  ![Sum.inl 1, Sum.inl 2, Sum.inr 0]

private def pairAPNRelabel : Fin 3 → Fin 4 ⊕ Fin 1 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inl 3]

private def pairBCBody : Lang0.BoundedFormula (Fin 4) 1 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairBCRelabel

private def pairAPNBody : Lang0.BoundedFormula (Fin 4) 1 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairAPNRelabel

/--
`pair3Graph(a,b,c,n)` holds iff `Nat.pair a (Nat.pair b c) = n`.
-/
def pair3Graph : Lang0.Formula (Fin 4) :=
  ∃' (pairBCBody ⊓ pairAPNBody)

theorem pair3Graph_realize (a b c n : ℕ) :
    pair3Graph.Realize ![a, b, c, n] ↔ Nat.pair a (Nat.pair b c) = n := by
  have h0 :
      pair3Graph.Realize ![a, b, c, n] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pair3Graph ![a, b, c, n]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := pair3Graph)
            (x := ![a, b, c, n]) (y := (default : Fin 0 → ℕ))).symm

  have hSnoc0 {p : Fin 0 → ℕ} {x : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p x 0 = x := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := x) (p := p) (n := 0))

  have hBCVal (p : ℕ) :
      (Sum.elim (![a, b, c, n] : Fin 4 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairBCRelabel) = ![b, c, p] := by
    funext j
    fin_cases j <;> simp [pairBCRelabel]

  have hAPNVal (p : ℕ) :
      (Sum.elim (![a, b, c, n] : Fin 4 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairAPNRelabel) = ![a, p, n] := by
    funext j
    fin_cases j <;> simp [pairAPNRelabel]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pair3Graph ![a, b, c, n]
          (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [pair3Graph] using h') with ⟨p, hp⟩
    have hBC : pairGraph.Realize ![b, c, p] := by
      have : pairGraph.Realize (Sum.elim (![a, b, c, n] : Fin 4 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) p) ∘
          pairBCRelabel) := by
        simpa [pairBCBody, hSnoc0] using hp.1
      simpa [hBCVal p] using this
    have hAPN : pairGraph.Realize ![a, p, n] := by
      have : pairGraph.Realize (Sum.elim (![a, b, c, n] : Fin 4 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) p) ∘
          pairAPNRelabel) := by
        simpa [pairAPNBody, hSnoc0] using hp.2
      simpa [hAPNVal p] using this
    have hPairBC : Nat.pair b c = p := (pairGraph_realize b c p).1 hBC
    have hPairAPN : Nat.pair a p = n := (pairGraph_realize a p n).1 hAPN
    simpa [hPairBC] using hPairAPN
  · intro hPair
    have hPairAPN : Nat.pair a (Nat.pair b c) = n := hPair
    have hBC : pairGraph.Realize ![b, c, Nat.pair b c] := (pairGraph_realize b c (Nat.pair b c)).2 rfl
    have hAPN : pairGraph.Realize ![a, Nat.pair b c, n] :=
      (pairGraph_realize a (Nat.pair b c) n).2 hPairAPN
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pair3Graph ![a, b, c, n]
          (default : Fin 0 → ℕ) := by
      simp [pair3Graph]
      refine ⟨Nat.pair b c, ?_⟩
      refine And.intro ?_ ?_
      · have : pairGraph.Realize (Sum.elim (![a, b, c, n] : Fin 4 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) (Nat.pair b c)) ∘ pairBCRelabel) := by
          simpa [hBCVal (Nat.pair b c)] using hBC
        simpa [pairBCBody, hSnoc0] using this
      · have : pairGraph.Realize (Sum.elim (![a, b, c, n] : Fin 4 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) (Nat.pair b c)) ∘ pairAPNRelabel) := by
          simpa [hAPNVal (Nat.pair b c)] using hAPN
        simpa [pairAPNBody, hSnoc0] using this
    exact (h0).2 h'

end Pure

end Arithmetic

end RevHalt

