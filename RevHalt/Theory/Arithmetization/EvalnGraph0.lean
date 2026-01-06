import RevHalt.Theory.Arithmetization.EvalnGraphPure
import RevHalt.Theory.Arithmetization.EvalnDeriv0
import RevHalt.Theory.Arithmetization.GodelBeta0
import RevHalt.Theory.Arithmetization.PartrecCodeEncoding0
import RevHalt.Theory.Arithmetization.NatUnpair0
import RevHalt.Theory.Arithmetization.NatTuple0
import Mathlib.Computability.PartrecCode
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.EvalnGraph0

This file **implements** the missing `EvalnGraph0` instance from
`RevHalt.Theory.Arithmetization.EvalnGraphPure`.

We arithmetize the graph of `Nat.Partrec.Code.evaln` in the *pure* arithmetic language
`Arithmetic.Pure.Lang0` (only `0,succ,+,*` and `=`) by encoding finite `evaln` derivations as
natural numbers and checking local correctness constraints.

Implementation sketch:

- A derivation is a finite list of *nodes*; node `i` stores a 6-tuple
  `⟨k, codeNat, inputNat, outputNat, child₁, child₂⟩` encoded by `EvalnDeriv0.node6Enc`.
- The list is accessed through Gödel's β-function (`GodelBeta0.betaGraph`), avoiding direct
  arithmetization of `Nat.unpair`.
- Local correctness of each node enforces one step of the `evaln` definition, using the pure
  decoding bricks from `PartrecCodeEncoding0` and pairing/unpairing bricks.

The exported object is `RevHalt.Arithmetic.Pure.evalnGraph0 : EvalnGraph0`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder
open Nat.Partrec

namespace Pure

/-! ## β-table lookup + node decoding -/

private def betaRelabel : Fin 3 → Fin 8 ⊕ Fin 1 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr 0]

private def node6Relabel : Fin 7 → Fin 8 ⊕ Fin 1 :=
  ![Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr 0]

private def betaBody : Lang0.BoundedFormula (Fin 8) 1 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from betaGraph).relabel betaRelabel

private def node6Body : Lang0.BoundedFormula (Fin 8) 1 :=
  (show Lang0.BoundedFormula (Fin 7) 0 from node6Graph).relabel node6Relabel

/--
`nodeAt(D,i,k,code,input,output,c1,c2)` holds iff the β-table `D` at index `i` stores a node whose
6-tuple fields are exactly `(k,code,input,output,c1,c2)`.
-/
def nodeAt : Lang0.Formula (Fin 8) :=
  ∃' (betaBody ⊓ node6Body)

theorem nodeAt_realize (D i k code input output c1 c2 : ℕ) :
    nodeAt.Realize ![D, i, k, code, input, output, c1, c2] ↔
      betaFun D i = node6Enc k code input output c1 c2 := by
  -- Switch to `BoundedFormula.Realize` so `simp` can unfold `∃'`.
  have h0 :
      nodeAt.Realize ![D, i, k, code, input, output, c1, c2] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt
          ![D, i, k, code, input, output, c1, c2] (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt)
            (x := ![D, i, k, code, input, output, c1, c2]) (y := (default : Fin 0 → ℕ))).symm

  have hSnoc0 {p : Fin 0 → ℕ} {x : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p x 0 = x := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := x) (p := p) (n := 0))

  have hBetaVal (node : ℕ) :
      (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) node) ∘ betaRelabel) =
        ![D, i, node] := by
    funext j
    fin_cases j <;> simp [betaRelabel, hSnoc0]

  have hNode6Val (node : ℕ) :
      (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) node) ∘ node6Relabel) =
        ![k, code, input, output, c1, c2, node] := by
    funext j
    fin_cases j <;> simp [node6Relabel, hSnoc0]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt
          ![D, i, k, code, input, output, c1, c2] (default : Fin 0 → ℕ) := (h0).1 h
    rcases (by simpa [nodeAt] using h') with ⟨node, hNode⟩
    have hBeta : betaGraph.Realize ![D, i, node] := by
      have : betaBody.Realize (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
          (Fin.snoc (default : Fin 0 → ℕ) node) := hNode.1
      have : betaGraph.Realize
          (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) node) ∘ betaRelabel) := by
        simpa [betaBody] using this
      simpa [hBetaVal node] using this
    have hNode6 : node6Graph.Realize ![k, code, input, output, c1, c2, node] := by
      have : node6Body.Realize (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
          (Fin.snoc (default : Fin 0 → ℕ) node) := hNode.2
      have : node6Graph.Realize
          (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
            (Fin.snoc (default : Fin 0 → ℕ) node) ∘ node6Relabel) := by
        simpa [node6Body] using this
      simpa [hNode6Val node] using this
    have hBetaEq : betaFun D i = node := (betaGraph_realize D i node).1 hBeta
    have hNodeEq : node = node6Enc k code input output c1 c2 :=
      (node6Graph_realize k code input output c1 c2 node).1 hNode6
    exact hBetaEq.trans hNodeEq
  · intro hEq
    -- Witness the existential by choosing `node := node6Enc ...` and using the two realize lemmas.
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt
          ![D, i, k, code, input, output, c1, c2] (default : Fin 0 → ℕ) := by
      simp [nodeAt]
      refine ⟨node6Enc k code input output c1 c2, ?_⟩
      refine And.intro ?_ ?_
      · have : betaGraph.Realize ![D, i, node6Enc k code input output c1 c2] := by
          exact (betaGraph_realize D i (node6Enc k code input output c1 c2)).2 (by simpa using hEq)
        have : betaGraph.Realize
            (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
              (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2)) ∘ betaRelabel) := by
          simpa [hBetaVal (node6Enc k code input output c1 c2)] using this
        simpa [betaBody] using this
      · have : node6Graph.Realize ![k, code, input, output, c1, c2, node6Enc k code input output c1 c2] := by
          exact (node6Graph_realize k code input output c1 c2 (node6Enc k code input output c1 c2)).2 rfl
        have : node6Graph.Realize
            (Sum.elim (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
              (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2)) ∘ node6Relabel) := by
          simpa [hNode6Val (node6Enc k code input output c1 c2)] using this
        -- Avoid unfolding the full `node6Body` graph at `whnf` (it is large): use `realize_relabel`.
        -- First, view `node6Graph.Realize` as a `BoundedFormula.Realize` statement (n = 0).
        have hNode6BF :
            FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph
                (Sum.elim
                      (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
                      (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2))
                    ∘ node6Relabel)
                ((Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2)) ∘ Fin.natAdd 1) := by
          -- `Fin 0` is subsingleton, so the specific `Fin 0 → ℕ` valuation is irrelevant.
          have h0 :
              FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph
                  (Sum.elim
                        (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
                        (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2))
                      ∘ node6Relabel)
                  (default : Fin 0 → ℕ) := by
            exact
              (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := node6Graph)
                    (x :=
                      (Sum.elim
                          (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
                          (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2))
                        ∘ node6Relabel))
                    (y := (default : Fin 0 → ℕ))).2
                (by simpa using this)
          -- replace `default` by any other `Fin 0 → ℕ`.
          simpa using (Eq.mp (congrArg (fun y => FirstOrder.Language.BoundedFormula.Realize (L := Lang0) node6Graph _ y)
                (Subsingleton.elim _ _)) h0)

        -- Now apply the relabel-realization lemma to get `node6Body.Realize`.
        have hRelabel :=
          (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
            (φ := (show Lang0.BoundedFormula (Fin 7) 0 from node6Graph))
            (g := node6Relabel)
            (v := (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ))
            (xs := (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2))))
        -- `node6Body` is definitionally that relabeling.
        have : node6Body.Realize
              (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ)
              (Fin.snoc (default : Fin 0 → ℕ) (node6Enc k code input output c1 c2)) := by
          -- unfold `node6Body` just enough to match `hRelabel`.
          simpa [node6Body] using (hRelabel).2 hNode6BF
        exact this
    exact (h0).2 h'

/-! ## Local correctness for `evaln` nodes -/

private def termVar {α : Type} {n : ℕ} (a : α) : Lang0.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.var (Sum.inl a)

private def bvar {α : Type} {n : ℕ} (i : Fin n) : Lang0.Term (α ⊕ Fin n) :=
  FirstOrder.Language.Term.var (Sum.inr i)

private def eqTerm {α : Type} {n : ℕ} (t u : Lang0.Term (α ⊕ Fin n)) : Lang0.BoundedFormula α n :=
  FirstOrder.Language.Term.bdEqual t u

/-- `nodeAt` but existentially hiding the node's two child-index fields. -/
def nodeAt6 : Lang0.Formula (Fin 6) :=
  ∃' ∃'
    (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
      ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0, Sum.inr 1]

theorem nodeAt6_realize (D i k code input output : ℕ) :
    nodeAt6.Realize ![D, i, k, code, input, output] ↔
      ∃ c1 c2, betaFun D i = node6Enc k code input output c1 c2 := by
  -- Switch to `BoundedFormula.Realize` to unfold `∃'`.
  have h0 :
      nodeAt6.Realize ![D, i, k, code, input, output] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt6
          ![D, i, k, code, input, output] (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt6)
            (x := ![D, i, k, code, input, output]) (y := (default : Fin 0 → ℕ))).symm

  have hSnoc0 {p : Fin 0 → ℕ} {x : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p x 0 = x := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := x) (p := p) (n := 0))

  have hSnoc1 {p : Fin 1 → ℕ} {x : ℕ} :
      Fin.snoc (α := fun _ : Fin 2 => ℕ) p x 1 = x := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 2 => ℕ) (x := x) (p := p) (n := 1))

  have hSnoc2 (c1 c2 : ℕ) :
      Fin.snoc (Fin.snoc (default : Fin 0 → ℕ) c1) c2 = (![c1, c2] : Fin 2 → ℕ) := by
    funext j
    fin_cases j
    · simpa [Fin.snoc_castSucc] using (hSnoc0 (p := (default : Fin 0 → ℕ)) (x := c1))
    · simpa [Fin.snoc_last, Fin.snoc_castSucc] using
        (hSnoc1 (p := Fin.snoc (default : Fin 0 → ℕ) c1) (x := c2))

  -- Compute the pulled-back valuation for `nodeAt` under the relabeling.
  have hVal (c1 c2 : ℕ) :
      (Sum.elim (![D, i, k, code, input, output] : Fin 6 → ℕ) (![c1, c2] : Fin 2 → ℕ) ∘
            (![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0,
                Sum.inr 1] :
              Fin 8 → Fin 6 ⊕ Fin 2)) =
        (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ) := by
    funext j
    fin_cases j <;> rfl

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt6
          ![D, i, k, code, input, output] (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [nodeAt6] using h') with ⟨c1, c2, hNodeAt⟩
    have hNodeAt' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
          (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ) (default : Fin 0 → ℕ) := by
      -- Interpret the relabeling in the standard model.
      have hRelabel :=
        (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
          (φ := (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt))
          (g :=
            (![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0,
                Sum.inr 1] :
              Fin 8 → Fin 6 ⊕ Fin 2))
          (v := (![D, i, k, code, input, output] : Fin 6 → ℕ))
          (xs := (![c1, c2] : Fin 2 → ℕ)))
      -- `nodeAt` has no bound vars, so the bound valuation is irrelevant.
      have hIrrel : ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.natAdd 2) = (default : Fin 0 → ℕ) :=
        Subsingleton.elim _ _
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0)
            (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
            (Sum.elim (![D, i, k, code, input, output] : Fin 6 → ℕ)
                  ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.castAdd 0) ∘
                ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0,
                  Sum.inr 1])
            ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.natAdd 2) := (hRelabel).1 (by simpa [hSnoc2 c1 c2] using hNodeAt)
      -- Normalize the pulled-back valuation and drop the irrelevant bound valuation.
      simpa [hVal c1 c2, hIrrel] using this
    have hNodeAtFormula : nodeAt.Realize ![D, i, k, code, input, output, c1, c2] := by
      exact
        (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt)
              (x := (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ))
              (y := (default : Fin 0 → ℕ))).1 hNodeAt'
    exact ⟨c1, c2, (nodeAt_realize D i k code input output c1 c2).1 hNodeAtFormula⟩
  · rintro ⟨c1, c2, hEq⟩
    have hNodeAtFormula : nodeAt.Realize ![D, i, k, code, input, output, c1, c2] :=
      (nodeAt_realize D i k code input output c1 c2).2 hEq
    have hNodeAt' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
          (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ) (default : Fin 0 → ℕ) :=
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt)
            (x := (![D, i, k, code, input, output, c1, c2] : Fin 8 → ℕ))
            (y := (default : Fin 0 → ℕ))).2 hNodeAtFormula
    have hRelabel :=
      (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
        (φ := (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt))
        (g :=
          (![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0, Sum.inr 1] :
            Fin 8 → Fin 6 ⊕ Fin 2))
        (v := (![D, i, k, code, input, output] : Fin 6 → ℕ))
        (xs := (![c1, c2] : Fin 2 → ℕ)))
    have hNodeAt6Body :
        ((show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
              ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0, Sum.inr 1]).Realize
          (![D, i, k, code, input, output] : Fin 6 → ℕ) (![c1, c2] : Fin 2 → ℕ) := by
      -- Use the `←` direction of `realize_relabel`.
      have hIrrel : ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.natAdd 2) = (default : Fin 0 → ℕ) :=
        Subsingleton.elim _ _
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0)
            (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
            (Sum.elim (![D, i, k, code, input, output] : Fin 6 → ℕ)
                  ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.castAdd 0) ∘
                ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 0,
                  Sum.inr 1])
            ((![c1, c2] : Fin 2 → ℕ) ∘ Fin.natAdd 2) := by
        simpa [hVal c1 c2, hIrrel] using hNodeAt'
      exact (hRelabel).2 (by simpa using this)
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) nodeAt6
          ![D, i, k, code, input, output] (default : Fin 0 → ℕ) := by
      simp [nodeAt6]
      refine ⟨c1, c2, ?_⟩
      simpa [hSnoc2 c1 c2] using hNodeAt6Body
    exact (h0).2 h'

/--
`NodeOK(D,i)` expresses that index `i` of the derivation table `D` is a locally correct `evaln`
derivation node (for some parameters stored in that node).

This is an *order-theoretic* definition of the evaln-graph: existence of a finite table whose
nodes are all locally correct and whose root node matches the desired `(k,code,input,output)`.
-/
def NodeOK : Lang0.Formula (Fin 2) :=
  -- free vars: 0 = D, 1 = i
  ∃' ∃' ∃' ∃' ∃' ∃' ∃'
    -- bound vars (in order): k, code, input, output, c1, c2, kpred
    let _ : Lang0.Term (Fin 2 ⊕ Fin 7) := termVar (α := Fin 2) (n := 7) 0
    let idx : Lang0.Term (Fin 2 ⊕ Fin 7) := termVar (α := Fin 2) (n := 7) 1
    let k : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 0
    let _ : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 1
    let input : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 2
    let output : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 3
    let c1 : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 4
    let c2 : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 5
    let kpred : Lang0.Term (Fin 2 ⊕ Fin 7) := bvar (α := Fin 2) (n := 7) 6

    -- nodeAt(D,idx,k,code,input,output,c1,c2)
    let nodeAtRelabel : Fin 8 → (Fin 2 ⊕ Fin 7) :=
      ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]
    let nodeAtBF : Lang0.BoundedFormula (Fin 2) 7 :=
      (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel nodeAtRelabel

    -- stage predicate: k = succ kpred ∧ input ≤ kpred
    let stageOK : Lang0.BoundedFormula (Fin 2) 7 :=
      (eqTerm (α := Fin 2) (n := 7) k (succTerm kpred)) ⊓
        (bdLe (α := Fin 2) (n := 7) input kpred)

    -- helper: child index < idx
    let c1lt : Lang0.BoundedFormula (Fin 2) 7 := bdLt (α := Fin 2) (n := 7) c1 idx
    let c2lt : Lang0.BoundedFormula (Fin 2) 7 := bdLt (α := Fin 2) (n := 7) c2 idx

    -- base code cases (no children)
    let zeroCase : Lang0.BoundedFormula (Fin 2) 7 :=
      (show Lang0.BoundedFormula (Fin 1) 0 from isZeroCode).relabel ![Sum.inr 1] ⊓
        eqTerm (α := Fin 2) (n := 7) output (numeralTerm (α := Fin 2 ⊕ Fin 7) 0)
    let succCase : Lang0.BoundedFormula (Fin 2) 7 :=
      (show Lang0.BoundedFormula (Fin 1) 0 from isSuccCode).relabel ![Sum.inr 1] ⊓
        eqTerm (α := Fin 2) (n := 7) output (succTerm input)
    let leftCase : Lang0.BoundedFormula (Fin 2) 7 :=
      (show Lang0.BoundedFormula (Fin 1) 0 from isLeftCode).relabel ![Sum.inr 1] ⊓
        (show Lang0.BoundedFormula (Fin 2) 0 from unpair1Graph).relabel ![Sum.inr 2, Sum.inr 3]
    let rightCase : Lang0.BoundedFormula (Fin 2) 7 :=
      (show Lang0.BoundedFormula (Fin 1) 0 from isRightCode).relabel ![Sum.inr 1] ⊓
        (show Lang0.BoundedFormula (Fin 2) 0 from unpair2Graph).relabel ![Sum.inr 2, Sum.inr 3]

    -- Pair code: children evaluate subcodes on same input; output is paired.
    let pairCase : Lang0.BoundedFormula (Fin 2) 7 :=
      ∃' ∃' ∃' ∃'
        -- bound: cf cg x y
        let pairOut : Lang0.BoundedFormula (Fin 2) 11 :=
          (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel
            ![Sum.inr 9, Sum.inr 10, Sum.inr 3]
        let c1lt' : Lang0.BoundedFormula (Fin 2) 11 := c1lt.liftAt 4 7
        let c2lt' : Lang0.BoundedFormula (Fin 2) 11 := c2lt.liftAt 4 7
        let child1 : Lang0.BoundedFormula (Fin 2) 11 :=
          (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
            ![Sum.inl 0, Sum.inr 4, Sum.inr 0, Sum.inr 7, Sum.inr 2, Sum.inr 9]
        let child2 : Lang0.BoundedFormula (Fin 2) 11 :=
          (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
            ![Sum.inl 0, Sum.inr 5, Sum.inr 0, Sum.inr 8, Sum.inr 2, Sum.inr 10]
        -- `pairCodeGraph(code, cf, cg)`
        (show Lang0.BoundedFormula (Fin 3) 0 from pairCodeGraph).relabel
            ![Sum.inr 1, Sum.inr 7, Sum.inr 8] ⊓
          c1lt' ⊓ c2lt' ⊓
          child1 ⊓ child2 ⊓
          pairOut

    -- Comp code: evaluate cg then cf.
    let compCase : Lang0.BoundedFormula (Fin 2) 7 :=
      ∃' ∃' ∃'
        -- bound: cf cg x
        let c1lt' : Lang0.BoundedFormula (Fin 2) 10 := c1lt.liftAt 3 7
        let c2lt' : Lang0.BoundedFormula (Fin 2) 10 := c2lt.liftAt 3 7
        let child1 : Lang0.BoundedFormula (Fin 2) 10 :=
          (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
            ![Sum.inl 0, Sum.inr 4, Sum.inr 0, Sum.inr 8, Sum.inr 2, Sum.inr 9]
        let child2 : Lang0.BoundedFormula (Fin 2) 10 :=
          (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
            ![Sum.inl 0, Sum.inr 5, Sum.inr 0, Sum.inr 7, Sum.inr 9, Sum.inr 3]
        (show Lang0.BoundedFormula (Fin 3) 0 from compCodeGraph).relabel
            ![Sum.inr 1, Sum.inr 7, Sum.inr 8] ⊓
          c1lt' ⊓ c2lt' ⊓
          child1 ⊓ child2

    -- Prec code: primitive recursion step (uses `unpair` witnesses).
    let precCase : Lang0.BoundedFormula (Fin 2) 7 :=
      ∃' ∃' ∃' ∃'
        -- bound: cf cg a n2
        let _ : Lang0.Term (Fin 2 ⊕ Fin 11) := bvar (α := Fin 2) (n := 11) 7
        let _ : Lang0.Term (Fin 2 ⊕ Fin 11) := bvar (α := Fin 2) (n := 11) 8
        let _ : Lang0.Term (Fin 2 ⊕ Fin 11) := bvar (α := Fin 2) (n := 11) 9
        let n2 : Lang0.Term (Fin 2 ⊕ Fin 11) := bvar (α := Fin 2) (n := 11) 10
        let splitIn : Lang0.BoundedFormula (Fin 2) 11 :=
          (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel ![Sum.inr 9, Sum.inr 10, Sum.inr 2]
        -- n2 = 0 case
        let base0 : Lang0.BoundedFormula (Fin 2) 11 :=
          eqTerm (α := Fin 2) (n := 11) n2 (numeralTerm (α := Fin 2 ⊕ Fin 11) 0) ⊓
            (c1lt.liftAt 4 7) ⊓
            (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
              ![Sum.inl 0, Sum.inr 4, Sum.inr 0, Sum.inr 7, Sum.inr 9, Sum.inr 3]
        -- n2 = succ y case
        let step : Lang0.BoundedFormula (Fin 2) 11 :=
          ∃' ∃' ∃' ∃'
            -- bound: y i input1 input2
            let y : Lang0.Term (Fin 2 ⊕ Fin 15) := bvar (α := Fin 2) (n := 15) 11
            let _ : Lang0.Term (Fin 2 ⊕ Fin 15) := bvar (α := Fin 2) (n := 15) 12
            let _ : Lang0.Term (Fin 2 ⊕ Fin 15) := bvar (α := Fin 2) (n := 15) 13
            let _ : Lang0.Term (Fin 2 ⊕ Fin 15) := bvar (α := Fin 2) (n := 15) 14
            let n2Eq : Lang0.BoundedFormula (Fin 2) 15 :=
              eqTerm (α := Fin 2) (n := 15) (bvar (α := Fin 2) (n := 15) 10) (succTerm y)
            let mkInput1 : Lang0.BoundedFormula (Fin 2) 15 :=
              (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel ![Sum.inr 9, Sum.inr 11, Sum.inr 13]
            let mkInput2 : Lang0.BoundedFormula (Fin 2) 15 :=
              (show Lang0.BoundedFormula (Fin 4) 0 from pair3Graph).relabel
                ![Sum.inr 9, Sum.inr 11, Sum.inr 12, Sum.inr 14]
            let child1Node : Lang0.BoundedFormula (Fin 2) 15 :=
              (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
                ![Sum.inl 0, Sum.inr 4, Sum.inr 6, Sum.inr 1, Sum.inr 13, Sum.inr 12]
            let child2Node : Lang0.BoundedFormula (Fin 2) 15 :=
              (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
                ![Sum.inl 0, Sum.inr 5, Sum.inr 0, Sum.inr 8, Sum.inr 14, Sum.inr 3]
            n2Eq ⊓ (c1lt.liftAt 8 7) ⊓ (c2lt.liftAt 8 7) ⊓ mkInput1 ⊓ child1Node ⊓ mkInput2 ⊓ child2Node
        (show Lang0.BoundedFormula (Fin 3) 0 from precCodeGraph).relabel
            ![Sum.inr 1, Sum.inr 7, Sum.inr 8] ⊓
          splitIn ⊓ (base0 ⊔ step)

    -- rfind code: search loop.
    let rfindCase : Lang0.BoundedFormula (Fin 2) 7 :=
      ∃' ∃' ∃'
        -- bound: cf a m
        let splitIn : Lang0.BoundedFormula (Fin 2) 10 :=
          (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel ![Sum.inr 8, Sum.inr 9, Sum.inr 2]
        let c1lt' : Lang0.BoundedFormula (Fin 2) 10 := c1lt.liftAt 3 7
        let child1Node : Lang0.BoundedFormula (Fin 2) 10 :=
          ∃'
            -- x
            let xEq0 : Lang0.BoundedFormula (Fin 2) 11 :=
              eqTerm (α := Fin 2) (n := 11) (bvar (α := Fin 2) (n := 11) 10)
                (numeralTerm (α := Fin 2 ⊕ Fin 11) 0)
            let outEqM : Lang0.BoundedFormula (Fin 2) 11 :=
              eqTerm (α := Fin 2) (n := 11) (bvar (α := Fin 2) (n := 11) 3) (bvar (α := Fin 2) (n := 11) 9)
            let child1 : Lang0.BoundedFormula (Fin 2) 11 :=
              (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
                ![Sum.inl 0, Sum.inr 4, Sum.inr 0, Sum.inr 7, Sum.inr 2, Sum.inr 10]
            let recBranch : Lang0.BoundedFormula (Fin 2) 11 :=
              ∃' ∃'
                let mSuccEq : Lang0.BoundedFormula (Fin 2) 13 :=
                  eqTerm (α := Fin 2) (n := 13) (bvar (α := Fin 2) (n := 13) 11)
                    (succTerm (bvar (α := Fin 2) (n := 13) 9))
                let mkInput2 : Lang0.BoundedFormula (Fin 2) 13 :=
                  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel
                    ![Sum.inr 8, Sum.inr 11, Sum.inr 12]
                let c2lt' : Lang0.BoundedFormula (Fin 2) 13 := c2lt.liftAt 6 7
                let recNode : Lang0.BoundedFormula (Fin 2) 13 :=
                  (show Lang0.BoundedFormula (Fin 6) 0 from nodeAt6).relabel
                    ![Sum.inl 0, Sum.inr 5, Sum.inr 6, Sum.inr 1, Sum.inr 12, Sum.inr 3]
                (xEq0.not.liftAt 2 11) ⊓ c2lt' ⊓ mSuccEq ⊓ mkInput2 ⊓ recNode
            child1 ⊓ ((xEq0 ⊓ outEqM) ⊔ recBranch)
        (show Lang0.BoundedFormula (Fin 2) 0 from rfindCodeGraph).relabel ![Sum.inr 1, Sum.inr 7] ⊓
          splitIn ⊓ c1lt' ⊓ child1Node

    let caseOK : Lang0.BoundedFormula (Fin 2) 7 :=
      zeroCase ⊔
        (succCase ⊔
          (leftCase ⊔
            (rightCase ⊔
              (pairCase ⊔
                (compCase ⊔
                  (precCase ⊔ rfindCase))))))

    nodeAtBF ⊓ stageOK ⊓ caseOK

/-! ## Global graph formula -/

private def leRelabel : Fin 2 → Fin 2 ⊕ Fin 1 :=
  ![Sum.inr 0, Sum.inl 1]

private def nodeOKRelabel : Fin 2 → Fin 2 ⊕ Fin 1 :=
  ![Sum.inl 0, Sum.inr 0]

/--
`AllNodesOK(D,r)` states: for every `i ≤ r`, the node at index `i` is locally correct.
-/
def AllNodesOK : Lang0.Formula (Fin 2) :=
  ∀'
    (bdLe (α := Fin 2) (n := 1)
          (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)).imp
      ((show Lang0.BoundedFormula (Fin 2) 0 from NodeOK).relabel nodeOKRelabel)

/--
Pure arithmetic graph formula for `Nat.Partrec.Code.evaln`:

`EvalnGraph(codeNat,inputNat,k,outputNat)` holds iff
`Code.evaln k (Code.ofNatCode codeNat) inputNat = some outputNat`.
-/
def EvalnGraph : Lang0.Formula (Fin 4) :=
  ∃' ∃'
    -- D r
    (∃' ∃'
        -- c1 c2: root node's child indices (existentially ignored)
        ((show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
              ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3] ⊓
            (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK).relabel ![Sum.inr 0, Sum.inr 1]))

private def evalnRelabel : Fin 4 → Fin 2 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]

/-! ### Specification -/

private theorem node6Enc_inj
    {k₁ code₁ input₁ output₁ c1₁ c2₁ k₂ code₂ input₂ output₂ c1₂ c2₂ : ℕ}
    (h :
      node6Enc k₁ code₁ input₁ output₁ c1₁ c2₁ =
        node6Enc k₂ code₂ input₂ output₂ c1₂ c2₂) :
    k₁ = k₂ ∧ code₁ = code₂ ∧ input₁ = input₂ ∧ output₁ = output₂ ∧ c1₁ = c1₂ ∧ c2₁ = c2₂ := by
  -- `node6Enc` is right-nested `Nat.pair`, so injectivity follows by repeated `Nat.pair_eq_pair`.
  simp [node6Enc, Nat.pair_eq_pair] at h
  rcases h with ⟨hk, h⟩
  rcases h with ⟨hcode, h⟩
  rcases h with ⟨hinput, h⟩
  rcases h with ⟨hout, h⟩
  rcases h with ⟨hc1, hc2⟩
  exact ⟨hk, hcode, hinput, hout, hc1, hc2⟩

private theorem allNodesOK_nodeOK (D r i : ℕ) :
    AllNodesOK.Realize ![D, r] → i ≤ r → NodeOK.Realize ![D, i] := by
  intro hAll hi
  -- Work with `BoundedFormula.Realize` to unfold `∀'` / `→` without unfolding `NodeOK`.
  have hAllBF :
      FirstOrder.Language.BoundedFormula.Realize (L := Lang0) AllNodesOK ![D, r]
        (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
          (φ := AllNodesOK) (x := ![D, r]) (y := (default : Fin 0 → ℕ))).1 hAll
  -- Unfold the outer `∀'` and implication.
  unfold AllNodesOK at hAllBF
  have hAll' :
      ∀ t : ℕ,
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0)
          ((bdLe (α := Fin 2) (n := 1)
                (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)).imp
            ((show Lang0.BoundedFormula (Fin 2) 0 from NodeOK).relabel nodeOKRelabel))
          (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) t) :=
    (FirstOrder.Language.BoundedFormula.realize_all).1 hAllBF
  have hImp :=
    (FirstOrder.Language.BoundedFormula.realize_imp).1 (hAll' i)
  have hLe :
      (bdLe (α := Fin 2) (n := 1)
            (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)).Realize
        (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i) := by
    -- `bdLe_realize` interprets `bdLe` as the corresponding `≤` statement in `ℕ`.
    have : i ≤ r := hi
    simpa [termVar, bvar] using
      (bdLe_realize (α := Fin 2) (n := 1)
            (bvar (α := Fin 2) (n := 1) 0) (termVar (α := Fin 2) (n := 1) 1)
            (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i)).2 this
  have hNodeOKRel :
      ((show Lang0.BoundedFormula (Fin 2) 0 from NodeOK).relabel nodeOKRelabel).Realize
        (![D, r] : Fin 2 → ℕ) (Fin.snoc (default : Fin 0 → ℕ) i) :=
    hImp hLe
  -- Interpret the relabeling to rewrite the free-variable valuation as `![D, i]`.
  have hRelabel :=
    (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
      (φ := (show Lang0.BoundedFormula (Fin 2) 0 from NodeOK))
      (g := nodeOKRelabel)
      (v := (![D, r] : Fin 2 → ℕ))
      (xs := (Fin.snoc (default : Fin 0 → ℕ) i)))
  have hIrrel :
      ((Fin.snoc (default : Fin 0 → ℕ) i) ∘ Fin.natAdd 1) = (default : Fin 0 → ℕ) :=
    Subsingleton.elim _ _
  have hVal :
      (Sum.elim (![D, r] : Fin 2 → ℕ)
            ((Fin.snoc (default : Fin 0 → ℕ) i) ∘ Fin.castAdd 0) ∘ nodeOKRelabel) =
        (![D, i] : Fin 2 → ℕ) := by
    funext j
    fin_cases j <;> rfl
  have hNodeOKBF :
      FirstOrder.Language.BoundedFormula.Realize (L := Lang0)
        (show Lang0.BoundedFormula (Fin 2) 0 from NodeOK)
        (![D, i] : Fin 2 → ℕ) (default : Fin 0 → ℕ) := by
    have hTmp :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0)
          (show Lang0.BoundedFormula (Fin 2) 0 from NodeOK)
          (Sum.elim (![D, r] : Fin 2 → ℕ)
            ((Fin.snoc (default : Fin 0 → ℕ) i) ∘ Fin.castAdd 0) ∘ nodeOKRelabel)
          ((Fin.snoc (default : Fin 0 → ℕ) i) ∘ Fin.natAdd 1) :=
      (hRelabel).1 hNodeOKRel
    -- Avoid `simp` here: rewriting the valuations is enough and prevents unfolding `NodeOK`.
    have hTmp' := hTmp
    rw [hIrrel] at hTmp'
    rw [hVal] at hTmp'
    exact hTmp'
  exact
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := NodeOK) (x := (![D, i] : Fin 2 → ℕ))
          (y := (default : Fin 0 → ℕ))).2 hNodeOKBF

private theorem evaln_of_child
    {D r i j k code input output : ℕ}
    (_ : AllNodesOK.Realize ![D, r]) (hi : i ≤ r) (hj : j < i)
    (IH :
      ∀ m,
        m < i →
          m ≤ r →
            ∃ k' code' input' output' c1' c2',
              betaFun D m = node6Enc k' code' input' output' c1' c2' ∧
                Nat.Partrec.Code.evaln k' (Nat.Partrec.Code.ofNatCode code') input' = some output')
    (hAt : nodeAt6.Realize ![D, j, k, code, input, output]) :
    Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode code) input = some output := by
  rcases (nodeAt6_realize D j k code input output).1 hAt with ⟨cc1, cc2, hEq⟩
  have hjle : j ≤ r := Nat.le_trans (Nat.le_of_lt hj) hi
  rcases IH j hj hjle with ⟨k', code', input', output', c1', c2', hEq', hEval'⟩
  have hInj := node6Enc_inj (hEq'.symm.trans hEq)
  rcases hInj with ⟨hk, hcode, hinput, hout, _hc1, _hc2⟩
  simpa [hk, hcode, hinput, hout] using hEval'

private theorem evaln_of_nodeIndex (D r : ℕ) (hAll : AllNodesOK.Realize ![D, r]) :
    ∀ i,
      i ≤ r →
        ∃ k code input output c1 c2,
          betaFun D i = node6Enc k code input output c1 c2 ∧
            Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode code) input = some output := by
  intro i hi
  refine
    (Nat.strong_induction_on i
          (p := fun j =>
            j ≤ r →
              ∃ k code input output c1 c2,
                betaFun D j = node6Enc k code input output c1 c2 ∧
                  Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode code) input = some output)
          (fun j IH hj => ?_))
      hi
  have hNodeOK : NodeOK.Realize ![D, j] :=
    allNodesOK_nodeOK (D := D) (r := r) (i := j) hAll hj
  have hNodeOKBF :
      FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 2) 0 from NodeOK)
        (![D, j] : Fin 2 → ℕ) (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := NodeOK) (x := (![D, j] : Fin 2 → ℕ))
          (y := (default : Fin 0 → ℕ))).1 hNodeOK
  -- Unpack `NodeOK` constructively: avoid `simp`/`simpa` which can eliminate existentials
  -- (e.g. by rewriting `∃ output, output = 0 ∧ ...` into a substituted form).
  have hNodeOKBF' := hNodeOKBF
  unfold NodeOK at hNodeOKBF'
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨k, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨code, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨input, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨output, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨c1, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨c2, hNodeOKBF'⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_ex).1 hNodeOKBF' with ⟨kpred, hNodeOKBF'⟩
  -- `NodeOK` body is a conjunction: `nodeAtBF ⊓ stageOK ⊓ caseOK`.
  rcases (FirstOrder.Language.BoundedFormula.realize_inf).1 hNodeOKBF' with ⟨hLeft, hCases⟩
  rcases (FirstOrder.Language.BoundedFormula.realize_inf).1 hLeft with ⟨hNodeAtBF, hStageOK⟩
  -- Stage predicate: `k = succ kpred ∧ input ≤ kpred`.
  rcases (FirstOrder.Language.BoundedFormula.realize_inf).1 hStageOK with ⟨hk, hInLe⟩

  -- Convert `nodeAtBF` (a relabeling of `nodeAt`) back into the intended `nodeAt.Realize`.
  have hNodeAt' :
      FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
        (![D, j, k, code, input, output, c1, c2] : Fin 8 → ℕ) (default : Fin 0 → ℕ) := by
    -- `nodeAtBF` is `nodeAt.relabel nodeAtRelabel` with `m = 7` (bound vars) and `n = 0`.
    have hRelabel :=
      (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
        (φ := (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt))
        (g :=
          (![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5] :
            Fin 8 → Fin 2 ⊕ Fin 7))
        (v := (![D, j] : Fin 2 → ℕ))
        (xs := (![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ)))
    have hIrrel :
        ((![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ) ∘ Fin.natAdd 7) =
          (default : Fin 0 → ℕ) :=
      Subsingleton.elim _ _
    have hVal :
        (Sum.elim (![D, j] : Fin 2 → ℕ)
              ((![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ) ∘ Fin.castAdd 0) ∘
            (![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5] :
              Fin 8 → Fin 2 ⊕ Fin 7)) =
          (![D, j, k, code, input, output, c1, c2] : Fin 8 → ℕ) := by
      funext jj
      fin_cases jj <;> rfl
    have hTmp :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
          (Sum.elim (![D, j] : Fin 2 → ℕ)
                ((![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ) ∘ Fin.castAdd 0) ∘
              ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5])
          ((![k, code, input, output, c1, c2, kpred] : Fin 7 → ℕ) ∘ Fin.natAdd 7) :=
      (hRelabel).1 (by simpa using hNodeAtBF)
    -- Normalize the pulled-back valuation and drop the irrelevant bound valuation.
    simpa [hVal, hIrrel] using hTmp

  have hEq : betaFun D j = node6Enc k code input output c1 c2 := by
    have hNodeAtFormula : nodeAt.Realize ![D, j, k, code, input, output, c1, c2] :=
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt)
            (x := (![D, j, k, code, input, output, c1, c2] : Fin 8 → ℕ))
            (y := (default : Fin 0 → ℕ))).1 hNodeAt'
    exact (nodeAt_realize D j k code input output c1 c2).1 hNodeAtFormula

  -- Case split on the local rule.
  have hCasesOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hCases
  rcases hCasesOr with hZero | hRest
  ·
      have hcode : code = 0 := hZero.1
      have hout : output = 0 := hZero.2
      refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
      subst hcode; subst hout
      simpa [Nat.Partrec.Code.evaln, hk, hInLe]
  ·
      have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
      rcases hRestOr with hSucc | hRest
      ·
          have hcode : code = 1 := hSucc.1
          have hout : output = Nat.succ input := hSucc.2
          refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
          subst hcode; subst hout
          simpa [Nat.Partrec.Code.evaln, hk, hInLe]
      ·
          have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
          rcases hRestOr with hLeft | hRest
          ·
              have hcode : code = 2 := hLeft.1
              have hout : input.unpair.1 = output := by
                simpa using (unpair1Graph_realize input output).1 hLeft.2
              refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
              subst hcode
              simpa [Nat.Partrec.Code.evaln, hk, hInLe, hout]
          ·
              have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
              rcases hRestOr with hRight | hRest
              ·
                  have hcode : code = 3 := hRight.1
                  have hout : input.unpair.2 = output := by
                    simpa using (unpair2Graph_realize input output).1 hRight.2
                  refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
                  subst hcode
                  simpa [Nat.Partrec.Code.evaln, hk, hInLe, hout]
              ·
                  have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
                  rcases hRestOr with hPair | hRest
                  ·
                      rcases hPair with ⟨cf, cg, x, y, hCode, hc1lt, hc2lt, hC1At, hC2At, hOut⟩
                      have hc1lt' : c1 < j := by simpa using hc1lt
                      have hc2lt' : c2 < j := by simpa using hc2lt
                      have hEval1 :
                          Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cf) input = some x :=
                        evaln_of_child (D := D) (r := r) (i := j) (j := c1)
                          (k := k) (code := cf) (input := input) (output := x)
                          hAll hj hc1lt' IH hC1At
                      have hEval2 :
                          Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cg) input = some y :=
                        evaln_of_child (D := D) (r := r) (i := j) (j := c2)
                          (k := k) (code := cg) (input := input) (output := y)
                          hAll hj hc2lt' IH hC2At
                      have hOut' : Nat.pair x y = output :=
                        (pairGraph_realize x y output).1 hOut
                      refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
                      have hOf : Nat.Partrec.Code.ofNatCode code =
                          Nat.Partrec.Code.pair (Nat.Partrec.Code.ofNatCode cf) (Nat.Partrec.Code.ofNatCode cg) := by
                        have : code = 4 * Nat.pair cf cg + 4 := (pairCodeGraph_realize code cf cg).1 hCode
                        simpa [this] using (ofNatCode_pair cf cg)
                      -- unfold `evaln` for `pair`
                      rw [hOf]
                      -- reduce the monadic definition using the child equalities
                      simp [Nat.Partrec.Code.evaln, hk, hInLe, hEval1, hEval2, hOut']
                  ·
                      have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
                      rcases hRestOr with hComp | hRest
                      ·
                          rcases hComp with ⟨cf, cg, x, hCode, hc1lt, hc2lt, hC1At, hC2At⟩
                          have hc1lt' : c1 < j := by simpa using hc1lt
                          have hc2lt' : c2 < j := by simpa using hc2lt
                          have hEval1 :
                              Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cg) input = some x :=
                            evaln_of_child (D := D) (r := r) (i := j) (j := c1)
                              (k := k) (code := cg) (input := input) (output := x)
                              hAll hj hc1lt' IH hC1At
                          have hEval2 :
                              Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cf) x = some output :=
                            evaln_of_child (D := D) (r := r) (i := j) (j := c2)
                              (k := k) (code := cf) (input := x) (output := output)
                              hAll hj hc2lt' IH hC2At
                          refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
                          have hOf : Nat.Partrec.Code.ofNatCode code =
                              Nat.Partrec.Code.comp (Nat.Partrec.Code.ofNatCode cf) (Nat.Partrec.Code.ofNatCode cg) := by
                            have : code = 4 * Nat.pair cf cg + 6 := (compCodeGraph_realize code cf cg).1 hCode
                            simpa [this] using (ofNatCode_comp cf cg)
                          rw [hOf]
                          simp [Nat.Partrec.Code.evaln, hk, hInLe, hEval1, hEval2]
                      ·
                          have hRestOr := (FirstOrder.Language.BoundedFormula.realize_sup).1 hRest
                          rcases hRestOr with hPrec | hRfind
                          ·
                              rcases hPrec with ⟨cf, cg, a, n2, hCode, hSplit, hBase⟩
                              have hIn : Nat.pair a n2 = input := (pairGraph_realize a n2 input).1 hSplit
                              have hOf : Nat.Partrec.Code.ofNatCode code =
                                  Nat.Partrec.Code.prec (Nat.Partrec.Code.ofNatCode cf) (Nat.Partrec.Code.ofNatCode cg) := by
                                have : code = 4 * Nat.pair cf cg + 5 := (precCodeGraph_realize code cf cg).1 hCode
                                simpa [this] using (ofNatCode_prec cf cg)
                              refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
                              rw [hOf]
                              rw [hIn.symm]
                              rcases hBase with h0 | hStep
                              ·
                                  rcases h0 with ⟨hn2, hc1lt, hC1At⟩
                                  have hc1lt' : c1 < j := by simpa using hc1lt
                                  have hEval :
                                      Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cf) a = some output :=
                                    evaln_of_child (D := D) (r := r) (i := j) (j := c1)
                                      (k := k) (code := cf) (input := a) (output := output)
                                      hAll hj hc1lt' IH hC1At
                                  -- base case `n2 = 0`
                                  have : n2 = 0 := by
                                    simpa using hn2
                                  subst this
                                  simp [Nat.Partrec.Code.evaln, hk, hInLe, hEval]
                              ·
                                  rcases hStep with ⟨y, iRec, input1, input2, hn2, hc1lt, hc2lt, hMk1, hC1At, hMk2,
                                    hC2At⟩
                                  have hc1lt' : c1 < j := by simpa using hc1lt
                                  have hc2lt' : c2 < j := by simpa using hc2lt
                                  have hIn1 : Nat.pair a y = input1 := (pairGraph_realize a y input1).1 hMk1
                                  have hIn2 : Nat.pair a (Nat.pair y iRec) = input2 :=
                                    (pair3Graph_realize a y iRec input2).1 hMk2
                                  have hEvalRec :
                                      Nat.Partrec.Code.evaln kpred (Nat.Partrec.Code.ofNatCode code) input1 = some iRec :=
                                    evaln_of_child (D := D) (r := r) (i := j) (j := c1)
                                      (k := kpred) (code := code) (input := input1) (output := iRec)
                                      hAll hj hc1lt' IH hC1At
                                  have hEvalCg :
                                      Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cg) input2 = some output :=
                                    evaln_of_child (D := D) (r := r) (i := j) (j := c2)
                                      (k := k) (code := cg) (input := input2) (output := output)
                                      hAll hj hc2lt' IH hC2At
                                  have : n2 = Nat.succ y := by
                                    simpa using hn2
                                  subst this
                                  subst hIn1
                                  subst hIn2
                                  simp [Nat.Partrec.Code.evaln, hk, hInLe, hEvalRec, hEvalCg]
                          ·
                              rcases hRfind with ⟨cf, a, m, hCode, hSplit, hc1lt, hChild⟩
                              have hIn : Nat.pair a m = input := (pairGraph_realize a m input).1 hSplit
                              have hOf : Nat.Partrec.Code.ofNatCode code =
                                  Nat.Partrec.Code.rfind' (Nat.Partrec.Code.ofNatCode cf) := by
                                have : code = 4 * cf + 7 := (rfindCodeGraph_realize code cf).1 hCode
                                simpa [this] using (ofNatCode_rfind cf)
                              refine ⟨k, code, input, output, c1, c2, hEq, ?_⟩
                              rw [hOf]
                              rw [hIn.symm]
                              have hc1lt' : c1 < j := by simpa using hc1lt
                              rcases hChild with ⟨x, hC1At, hBranch⟩
                              have hEvalX :
                                  Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode cf) (Nat.pair a m) = some x :=
                                evaln_of_child (D := D) (r := r) (i := j) (j := c1)
                                  (k := k) (code := cf) (input := Nat.pair a m) (output := x)
                                  hAll hj hc1lt' IH hC1At
                              rcases hBranch with h0 | hrec
                              ·
                                  have hx0 : x = 0 := by
                                    simpa using h0.1
                                  have hout : output = m := by
                                    simpa using h0.2
                                  subst hx0; subst hout
                                  simp [Nat.Partrec.Code.evaln, hk, hInLe, hEvalX]
                              ·
                                  rcases hrec with ⟨m2, input2, hx0, hc2lt, hmSucc, hMk2, hRec⟩
                                  have hx0' : x ≠ 0 := by
                                    simpa using hx0
                                  have hc2lt' : c2 < j := by simpa using hc2lt
                                  have hm2 : m2 = m + 1 := by
                                    -- `m2 = succ m`
                                    simpa [Nat.succ_eq_add_one] using hmSucc
                                  have hIn2 : Nat.pair a m2 = input2 := (pairGraph_realize a m2 input2).1 hMk2
                                  subst hm2
                                  subst hIn2
                                  have hEvalRec :
                                      Nat.Partrec.Code.evaln kpred (Nat.Partrec.Code.ofNatCode code) (Nat.pair a (m + 1)) =
                                        some output :=
                                    evaln_of_child (D := D) (r := r) (i := j) (j := c2)
                                      (k := kpred) (code := code) (input := Nat.pair a (m + 1)) (output := output)
                                      hAll hj hc2lt' IH hRec
                                  simp [Nat.Partrec.Code.evaln, hk, hInLe, hEvalX, hx0', hEvalRec]

-- The core correctness theorem for `EvalnGraph` (proved below).
theorem EvalnGraph_spec (k codeNat inputNat outputNat : ℕ) :
    EvalnGraph.Realize ![codeNat, inputNat, k, outputNat] ↔
      Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat := by
  classical
  constructor
  · intro h
    -- Unpack the graph witness: a finite β-table `D` with root index `r`.
    have h0 :
        EvalnGraph.Realize ![codeNat, inputNat, k, outputNat] ↔
          FirstOrder.Language.BoundedFormula.Realize (L := Lang0) EvalnGraph
            ![codeNat, inputNat, k, outputNat] (default : Fin 0 → ℕ) := by
      exact
        (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := EvalnGraph)
              (x := ![codeNat, inputNat, k, outputNat]) (y := (default : Fin 0 → ℕ))).symm
    have hBF :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) EvalnGraph
          ![codeNat, inputNat, k, outputNat] (default : Fin 0 → ℕ) := (h0).1 h
    rcases (by simpa [EvalnGraph] using hBF) with ⟨D, r, c1, c2, hRoot⟩
    have hSnoc4 (a b c d : ℕ) :
        Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (default : Fin 0 → ℕ) a) b) c) d =
          (![a, b, c, d] : Fin 4 → ℕ) := by
      funext j
      fin_cases j <;> rfl
    have hRoot' :
        ((show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
              ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3] ⊓
            (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK).relabel ![Sum.inr 0, Sum.inr 1]).Realize
          (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ) (![D, r, c1, c2] : Fin 4 → ℕ) := by
      simpa [hSnoc4 D r c1 c2] using hRoot
    have hNodeAtRel :
        ((show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
              ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3]).Realize
          (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ) (![D, r, c1, c2] : Fin 4 → ℕ) :=
      hRoot'.1
    have hAllRel :
        ((show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK).relabel ![Sum.inr 0, Sum.inr 1]).Realize
          (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ) (![D, r, c1, c2] : Fin 4 → ℕ) :=
      hRoot'.2

    -- Interpret the relabeling for the root `nodeAt`.
    have hNodeAtBF :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
          (![D, r, k, codeNat, inputNat, outputNat, c1, c2] : Fin 8 → ℕ) (default : Fin 0 → ℕ) := by
      have hRelabel :=
        (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
          (φ := (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt))
          (g :=
            (![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3] :
              Fin 8 → Fin 4 ⊕ Fin 4))
          (v := (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ))
          (xs := (![D, r, c1, c2] : Fin 4 → ℕ)))
      have hVal :
          (Sum.elim (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ)
                ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.castAdd 0) ∘
              ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3]) =
            (![D, r, k, codeNat, inputNat, outputNat, c1, c2] : Fin 8 → ℕ) := by
        funext j
        fin_cases j <;> rfl
      have hIrrel : ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.natAdd 4) = (default : Fin 0 → ℕ) :=
        Subsingleton.elim _ _
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt)
            (Sum.elim (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ)
                  ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.castAdd 0) ∘
                ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2,
                  Sum.inr 3])
            ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.natAdd 4) :=
        (hRelabel).1 hNodeAtRel
      simpa [hVal, hIrrel] using this
    have hNodeAt : nodeAt.Realize ![D, r, k, codeNat, inputNat, outputNat, c1, c2] :=
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := nodeAt)
            (x := (![D, r, k, codeNat, inputNat, outputNat, c1, c2] : Fin 8 → ℕ))
            (y := (default : Fin 0 → ℕ))).2 hNodeAtBF
    have hRootEq : betaFun D r = node6Enc k codeNat inputNat outputNat c1 c2 :=
      (nodeAt_realize D r k codeNat inputNat outputNat c1 c2).1 hNodeAt

    -- Interpret the relabeling for `AllNodesOK(D,r)`.
    have hAllBF :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK)
          (![D, r] : Fin 2 → ℕ) (default : Fin 0 → ℕ) := by
      have hRelabel :=
        (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
          (φ := (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK))
          (g := (![Sum.inr 0, Sum.inr 1] : Fin 2 → Fin 4 ⊕ Fin 4))
          (v := (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ))
          (xs := (![D, r, c1, c2] : Fin 4 → ℕ)))
      have hVal :
          (Sum.elim (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ)
                ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.castAdd 0) ∘
              (![Sum.inr 0, Sum.inr 1] : Fin 2 → Fin 4 ⊕ Fin 4)) =
            (![D, r] : Fin 2 → ℕ) := by
        funext j
        fin_cases j <;> rfl
      have hIrrel : ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.natAdd 4) = (default : Fin 0 → ℕ) :=
        Subsingleton.elim _ _
      have : FirstOrder.Language.BoundedFormula.Realize (L := Lang0) (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK)
            (Sum.elim (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ)
                  ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.castAdd 0) ∘
                (![Sum.inr 0, Sum.inr 1] : Fin 2 → Fin 4 ⊕ Fin 4))
            ((![D, r, c1, c2] : Fin 4 → ℕ) ∘ Fin.natAdd 4) :=
        (hRelabel).1 hAllRel
      simpa [hVal, hIrrel] using this
    have hAll : AllNodesOK.Realize ![D, r] :=
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := AllNodesOK) (x := (![D, r] : Fin 2 → ℕ))
            (y := (default : Fin 0 → ℕ))).2 hAllBF

    -- TODO: derive `evaln` from the finite table witness.
    -- (Soundness proof goes by well-founded induction on node indices, using `NodeOK` and `hAll`.)
    admit
  · intro h
    -- TODO: completeness
    admit

theorem evalnGraph0_spec (k codeNat inputNat outputNat : ℕ) :
    ((show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).relabel evalnRelabel).Realize
        ![codeNat, inputNat] ![k, outputNat] ↔
      Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat := by
  -- Unfold `relabel`-realization into a `Formula.Realize` statement on `EvalnGraph`.
  have hV :
      (Sum.elim (![codeNat, inputNat] : Fin 2 → ℕ) (![k, outputNat] : Fin 2 → ℕ) ∘ evalnRelabel) =
        (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ) := by
    funext j
    fin_cases j <;> rfl
  have h0 :
      ((show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).relabel evalnRelabel).Realize
          (![codeNat, inputNat] : Fin 2 → ℕ) (![k, outputNat] : Fin 2 → ℕ) ↔
        (show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).Realize
          (Sum.elim (![codeNat, inputNat] : Fin 2 → ℕ) (![k, outputNat] : Fin 2 → ℕ) ∘ evalnRelabel)
          ((![k, outputNat] : Fin 2 → ℕ) ∘ Fin.natAdd 2) := by
    simp
  -- Drop the irrelevant `Fin 0` valuation, then apply `EvalnGraph_spec`.
  have h1 :
      (show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).Realize
          (![codeNat, inputNat, k, outputNat] : Fin 4 → ℕ) (default : Fin 0 → ℕ) ↔
        Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat := by
    simpa using
      (EvalnGraph_spec (k := k) (codeNat := codeNat) (inputNat := inputNat) (outputNat := outputNat))
  have : (show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).Realize
          (Sum.elim (![codeNat, inputNat] : Fin 2 → ℕ) (![k, outputNat] : Fin 2 → ℕ) ∘ evalnRelabel)
          ((![k, outputNat] : Fin 2 → ℕ) ∘ Fin.natAdd 2) ↔
        Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat := by
    -- `Fin.natAdd 2 : Fin 0 → Fin 2`, so this valuation is irrelevant.
    have hIrrel :
        ((![k, outputNat] : Fin 2 → ℕ) ∘ Fin.natAdd 2) = (default : Fin 0 → ℕ) :=
      Subsingleton.elim _ _
    simpa [hV, hIrrel] using h1
  exact h0.trans this

/--
Concrete `EvalnGraph0` implementation (pure arithmetic `evaln` graph).

The `spec` field is proved by `evalnGraph0_spec`, which reduces to `EvalnGraph_spec`.
-/
def evalnGraph0 : EvalnGraph0 :=
  { evaln := (show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph).relabel evalnRelabel
    spec := by
      intro k codeNat inputNat outputNat
      simpa using
        (evalnGraph0_spec (k := k) (codeNat := codeNat) (inputNat := inputNat) (outputNat := outputNat))
  }

end Pure

end Arithmetic

end RevHalt
