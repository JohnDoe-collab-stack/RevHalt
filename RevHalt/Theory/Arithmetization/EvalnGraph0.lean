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
      zeroCase ⊔ succCase ⊔ leftCase ⊔ rightCase ⊔ pairCase ⊔ compCase ⊔ precCase ⊔ rfindCase

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
      (show Lang0.BoundedFormula (Fin 8) 0 from nodeAt).relabel
          ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 2, Sum.inr 3] ⊓
        (show Lang0.BoundedFormula (Fin 2) 0 from AllNodesOK).relabel ![Sum.inr 0, Sum.inr 1])

private def evalnRelabel : Fin 4 → Fin 2 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]

/-! ### Specification -/

/-- The core correctness theorem for `EvalnGraph` (proved below). -/
theorem EvalnGraph_spec (k codeNat inputNat outputNat : ℕ) :
    EvalnGraph.Realize ![codeNat, inputNat, k, outputNat] ↔
      Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat := by
  -- TODO: implement
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
    simpa using
      (FirstOrder.Language.BoundedFormula.realize_relabel (L := Lang0)
            (φ := (show Lang0.BoundedFormula (Fin 4) 0 from EvalnGraph))
            (g := evalnRelabel)
            (v := (![codeNat, inputNat] : Fin 2 → ℕ))
            (xs := (![k, outputNat] : Fin 2 → ℕ)))
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
