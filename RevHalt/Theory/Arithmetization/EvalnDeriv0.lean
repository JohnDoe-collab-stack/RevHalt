import RevHalt.Theory.Arithmetization.GodelBeta0
import RevHalt.Theory.Arithmetization.NatTuple0
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.EvalnDeriv0

Data-encoding bricks for the “full arithmetization” track.

The eventual goal is to define a *pure* (`Lang0`) graph formula for
`Nat.Partrec.Code.evaln` (see `EvalnGraphPure.lean`). A standard approach is to
encode finite derivations / computation DAGs as natural numbers and then express
local correctness constraints arithmetically.

This file starts that infrastructure by defining a reusable encoding for
6-tuples via iterated `Nat.pair`, together with a pure graph formula and a
standard-model correctness lemma.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-! ### A 6-tuple encoding (right-nested pairing) -/

/--
Meta-level 6-tuple encoding used for derivation nodes:

`⟨k, codeNat, inputNat, outputNat, child₁, child₂⟩`

encoded as:

`Nat.pair k (Nat.pair codeNat (Nat.pair inputNat (Nat.pair outputNat (Nat.pair child₁ child₂))))`.
-/
def node6Enc (k codeNat inputNat outputNat child₁ child₂ : ℕ) : ℕ :=
  Nat.pair k (Nat.pair codeNat (Nat.pair inputNat (Nat.pair outputNat (Nat.pair child₁ child₂))))

private def p0Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inr 0)

private def p1Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inr 1)

private def p2Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inr 2)

private def p3Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inr 3)

private def kVar : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

private def codeVar : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 1)

private def inputVar : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 2)

private def outputVar : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 3)

private def child1Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 4)

private def child2Var : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 5)

private def nodeVar : Lang0.Term (Fin 7 ⊕ Fin 4) :=
  FirstOrder.Language.Term.var (Sum.inl 6)

private def pairRelabel_c1c2 : Fin 3 → Fin 7 ⊕ Fin 4 :=
  ![Sum.inl 4, Sum.inl 5, Sum.inr 0]

private def pairRelabel_out_p0 : Fin 3 → Fin 7 ⊕ Fin 4 :=
  ![Sum.inl 3, Sum.inr 0, Sum.inr 1]

private def pairRelabel_in_p1 : Fin 3 → Fin 7 ⊕ Fin 4 :=
  ![Sum.inl 2, Sum.inr 1, Sum.inr 2]

private def pairRelabel_code_p2 : Fin 3 → Fin 7 ⊕ Fin 4 :=
  ![Sum.inl 1, Sum.inr 2, Sum.inr 3]

private def pairRelabel_k_p3 : Fin 3 → Fin 7 ⊕ Fin 4 :=
  ![Sum.inl 0, Sum.inr 3, Sum.inl 6]

private def pairBody (ρ : Fin 3 → Fin 7 ⊕ Fin 4) : Lang0.BoundedFormula (Fin 7) 4 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel ρ

private def node6Body : Lang0.BoundedFormula (Fin 7) 4 :=
  (((pairBody pairRelabel_c1c2) ⊓ (pairBody pairRelabel_out_p0)) ⊓ (pairBody pairRelabel_in_p1)) ⊓
    ((pairBody pairRelabel_code_p2) ⊓ (pairBody pairRelabel_k_p3))

/--
Pure graph formula for the `node6Enc` encoding.

`node6Graph(k, codeNat, inputNat, outputNat, child₁, child₂, node)` holds iff
`node = node6Enc k codeNat inputNat outputNat child₁ child₂`.
-/
def node6Graph : Lang0.Formula (Fin 7) :=
  ∃' ∃' ∃' ∃' node6Body

theorem node6Graph_realize (k codeNat inputNat outputNat child₁ child₂ node : ℕ) :
    node6Graph.Realize ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ↔
      node = node6Enc k codeNat inputNat outputNat child₁ child₂ := by
  have h0 :
      node6Graph.Realize ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph
          ![k, codeNat, inputNat, outputNat, child₁, child₂, node] (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := node6Graph)
            (x := ![k, codeNat, inputNat, outputNat, child₁, child₂, node])
            (y := (default : Fin 0 → ℕ))).symm

  have hSnoc4 (p0 p1 p2 p3 : ℕ) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (default : Fin 0 → ℕ) p0) p1) p2) p3 =
        (![p0, p1, p2, p3] : Fin 4 → ℕ) := by
    funext j
    fin_cases j <;> rfl

  have hVal_c1c2 (p0 p1 p2 p3 : ℕ) :
      (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
          (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_c1c2) =
        ![child₁, child₂, p0] := by
    funext j
    fin_cases j <;> simp [pairRelabel_c1c2]

  have hVal_out_p0 (p0 p1 p2 p3 : ℕ) :
      (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
          (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_out_p0) =
        ![outputNat, p0, p1] := by
    funext j
    fin_cases j <;> simp [pairRelabel_out_p0]

  have hVal_in_p1 (p0 p1 p2 p3 : ℕ) :
      (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
          (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_in_p1) =
        ![inputNat, p1, p2] := by
    funext j
    fin_cases j <;> simp [pairRelabel_in_p1]

  have hVal_code_p2 (p0 p1 p2 p3 : ℕ) :
      (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
          (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_code_p2) =
        ![codeNat, p2, p3] := by
    funext j
    fin_cases j <;> simp [pairRelabel_code_p2]

  have hVal_k_p3 (p0 p1 p2 p3 : ℕ) :
      (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
          (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_k_p3) =
        ![k, p3, node] := by
    funext j
    fin_cases j <;> simp [pairRelabel_k_p3]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph
          ![k, codeNat, inputNat, outputNat, child₁, child₂, node] (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [node6Graph] using h') with ⟨p0, p1, p2, p3, hp⟩
    have hpV :
        node6Body.Realize ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
      simpa [hSnoc4 p0 p1 p2 p3] using hp

    have hpVAnd :
        (((pairBody pairRelabel_c1c2).Realize
              ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] ∧
            (pairBody pairRelabel_out_p0).Realize
              ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) ∧
          (pairBody pairRelabel_in_p1).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) ∧
          ((pairBody pairRelabel_code_p2).Realize
              ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] ∧
            (pairBody pairRelabel_k_p3).Realize
              ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) := by
      simpa [node6Body] using hpV

    rcases hpVAnd with ⟨⟨⟨hC1C2Body, hOutP0Body⟩, hInP1Body⟩, ⟨hCodeP2Body, hKP3Body⟩⟩

    have hC1C2 : pairGraph.Realize ![child₁, child₂, p0] := by
      have : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_c1c2) := by
        simpa [pairBody] using hC1C2Body
      simpa [hVal_c1c2 p0 p1 p2 p3] using this

    have hOutP0 : pairGraph.Realize ![outputNat, p0, p1] := by
      have : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_out_p0) := by
        simpa [pairBody] using hOutP0Body
      simpa [hVal_out_p0 p0 p1 p2 p3] using this

    have hInP1 : pairGraph.Realize ![inputNat, p1, p2] := by
      have : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_in_p1) := by
        simpa [pairBody] using hInP1Body
      simpa [hVal_in_p1 p0 p1 p2 p3] using this

    have hCodeP2 : pairGraph.Realize ![codeNat, p2, p3] := by
      have : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_code_p2) := by
        simpa [pairBody] using hCodeP2Body
      simpa [hVal_code_p2 p0 p1 p2 p3] using this

    have hKP3 : pairGraph.Realize ![k, p3, node] := by
      have : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_k_p3) := by
        simpa [pairBody] using hKP3Body
      simpa [hVal_k_p3 p0 p1 p2 p3] using this

    have hp0 : Nat.pair child₁ child₂ = p0 := (pairGraph_realize child₁ child₂ p0).1 hC1C2
    have hp1 : Nat.pair outputNat p0 = p1 := (pairGraph_realize outputNat p0 p1).1 hOutP0
    have hp2 : Nat.pair inputNat p1 = p2 := (pairGraph_realize inputNat p1 p2).1 hInP1
    have hp3 : Nat.pair codeNat p2 = p3 := (pairGraph_realize codeNat p2 p3).1 hCodeP2
    have hNode : Nat.pair k p3 = node := (pairGraph_realize k p3 node).1 hKP3

    -- Collapse the intermediate equations to the right-nested encoding.
    have : node6Enc k codeNat inputNat outputNat child₁ child₂ = node := by
      simp [node6Enc, hp0, hp1, hp2, hp3, hNode]
    simpa [Eq.comm] using this.symm
  · intro hEq
    -- Pick the intermediate pairings as witnesses.
    let p0 := Nat.pair child₁ child₂
    let p1 := Nat.pair outputNat p0
    let p2 := Nat.pair inputNat p1
    let p3 := Nat.pair codeNat p2
    have hp0 : Nat.pair child₁ child₂ = p0 := rfl
    have hp1 : Nat.pair outputNat p0 = p1 := rfl
    have hp2 : Nat.pair inputNat p1 = p2 := rfl
    have hp3 : Nat.pair codeNat p2 = p3 := rfl
    have hNode : Nat.pair k p3 = node := by
      -- `hEq` is `node = node6Enc ...`; unfold `node6Enc` and read off the top-level pair.
      simpa [node6Enc, p0, p1, p2, p3] using hEq.symm

    have hpV :
        node6Body.Realize ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
      -- Discharge each `pairGraph` conjunct via `pairGraph_realize`.
      have hC1C2 : pairGraph.Realize ![child₁, child₂, p0] := (pairGraph_realize child₁ child₂ p0).2 hp0
      have hOutP0 : pairGraph.Realize ![outputNat, p0, p1] := (pairGraph_realize outputNat p0 p1).2 hp1
      have hInP1 : pairGraph.Realize ![inputNat, p1, p2] := (pairGraph_realize inputNat p1 p2).2 hp2
      have hCodeP2 : pairGraph.Realize ![codeNat, p2, p3] := (pairGraph_realize codeNat p2 p3).2 hp3
      have hKP3 : pairGraph.Realize ![k, p3, node] := (pairGraph_realize k p3 node).2 hNode

      -- Reinsert the relabelings.
      have hC1C2' : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_c1c2) := by
          simpa [hVal_c1c2 p0 p1 p2 p3] using hC1C2
      have hOutP0' : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_out_p0) := by
          simpa [hVal_out_p0 p0 p1 p2 p3] using hOutP0
      have hInP1' : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_in_p1) := by
          simpa [hVal_in_p1 p0 p1 p2 p3] using hInP1
      have hCodeP2' : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_code_p2) := by
          simpa [hVal_code_p2 p0 p1 p2 p3] using hCodeP2
      have hKP3' : pairGraph.Realize
          (Sum.elim (![k, codeNat, inputNat, outputNat, child₁, child₂, node] : Fin 7 → ℕ)
            (![p0, p1, p2, p3] : Fin 4 → ℕ) ∘ pairRelabel_k_p3) := by
          simpa [hVal_k_p3 p0 p1 p2 p3] using hKP3

      -- Pack the conjunctions back into `node6Body`.
      have hC1C2Body :
          (pairBody pairRelabel_c1c2).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
        simpa [pairBody] using hC1C2'
      have hOutP0Body :
          (pairBody pairRelabel_out_p0).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
        simpa [pairBody] using hOutP0'
      have hInP1Body :
          (pairBody pairRelabel_in_p1).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
        simpa [pairBody] using hInP1'
      have hCodeP2Body :
          (pairBody pairRelabel_code_p2).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
        simpa [pairBody] using hCodeP2'
      have hKP3Body :
          (pairBody pairRelabel_k_p3).Realize
            ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] := by
        simpa [pairBody] using hKP3'

      have hpVAnd :
          (((pairBody pairRelabel_c1c2).Realize
                ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] ∧
              (pairBody pairRelabel_out_p0).Realize
                ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) ∧
            (pairBody pairRelabel_in_p1).Realize
              ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) ∧
            ((pairBody pairRelabel_code_p2).Realize
                ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3] ∧
              (pairBody pairRelabel_k_p3).Realize
                ![k, codeNat, inputNat, outputNat, child₁, child₂, node] ![p0, p1, p2, p3]) := by
        exact
          And.intro
            (And.intro (And.intro hC1C2Body hOutP0Body) hInP1Body)
            (And.intro hCodeP2Body hKP3Body)

      simpa [node6Body] using hpVAnd

    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph
          ![k, codeNat, inputNat, outputNat, child₁, child₂, node] (default : Fin 0 → ℕ) := by
      simp [node6Graph]
      refine ⟨p0, p1, p2, p3, ?_⟩
      simpa [hSnoc4 p0 p1 p2 p3] using hpV
    exact (h0).2 h'

end Pure

end Arithmetic

end RevHalt
