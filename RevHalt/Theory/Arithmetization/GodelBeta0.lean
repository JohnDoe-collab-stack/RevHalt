import RevHalt.Theory.Arithmetization.NatMod0
import RevHalt.Theory.Arithmetization.NatPair0
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.GodelBeta0

Pure-arithmetic definability of Gödel's β-function graph.

We define the meta-level β-function:

`betaFun n i := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)`.

In the pure arithmetic language `Lang0` we do **not** arithmetize `Nat.unpair` directly (it uses
`sqrt` in its definition). Instead we existentially quantify witnesses `a b` such that
`Nat.pair a b = n` (using `pairGraph`), and express that `v` is the remainder of `a` modulo
`((i+1)*b+1)` using the term-level division witness `bdModPos`.

The main result is `betaGraph_realize`.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Pure

/-- Gödel β-function (as a meta-level function on `ℕ`). -/
def betaFun (n i : ℕ) : ℕ :=
  n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

private def nVar : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

private def iVar : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  FirstOrder.Language.Term.var (Sum.inl 1)

private def vVar : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  FirstOrder.Language.Term.var (Sum.inl 2)

private def aVar : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  FirstOrder.Language.Term.var (Sum.inr 0)

private def bVar : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  FirstOrder.Language.Term.var (Sum.inr 1)

private def modulus : Lang0.Term (Fin 3 ⊕ Fin 2) :=
  addTerm (mulTerm (succTerm iVar) bVar) (numeralTerm (α := Fin 3 ⊕ Fin 2) 1)

private def pairRelabel : Fin 3 → Fin 3 ⊕ Fin 2 :=
  ![Sum.inr 0, Sum.inr 1, Sum.inl 0]

private def pairBody : Lang0.BoundedFormula (Fin 3) 2 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairRelabel

private def modBody : Lang0.BoundedFormula (Fin 3) 2 :=
  bdModPos (α := Fin 3) (n := 2) aVar modulus vVar

/--
Pure arithmetic graph formula for Gödel's β-function:

`betaGraph(n,i,v)` holds iff `betaFun n i = v`.
-/
def betaGraph : Lang0.Formula (Fin 3) :=
  ∃' ∃' (pairBody ⊓ modBody)

theorem betaGraph_realize (n i v : ℕ) :
    betaGraph.Realize ![n, i, v] ↔ betaFun n i = v := by
  -- Switch to `BoundedFormula.Realize` (0 bound variables) so `simp` can expand `∃'` using
  -- `BoundedFormula.realize_ex`.
  have h0 :
      betaGraph.Realize ![n, i, v] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) betaGraph ![n, i, v]
          (default : Fin 0 → ℕ) := by
    exact
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize (φ := betaGraph) (x := ![n, i, v])
          (y := (default : Fin 0 → ℕ))).symm

  -- Normalization lemmas for the `∃'∃'`-generated `Fin.snoc` valuations.
  have hSnoc0 {p : Fin 0 → ℕ} {a : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p a 0 = a := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := a) (p := p) (n := 0))
  have hSnoc1 {p : Fin 1 → ℕ} {b : ℕ} :
      Fin.snoc (α := fun _ : Fin 2 => ℕ) p b 1 = b := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 2 => ℕ) (x := b) (p := p) (n := 1))

  have hSnoc2 (a b : ℕ) :
      Fin.snoc (Fin.snoc (default : Fin 0 → ℕ) a) b = (![a, b] : Fin 2 → ℕ) := by
    funext j
    fin_cases j
    · -- j = 0
      simpa [Fin.snoc_castSucc] using (hSnoc0 (p := (default : Fin 0 → ℕ)) (a := a))
    · -- j = 1
      simpa [Fin.snoc_last, Fin.snoc_castSucc] using (hSnoc1 (p := Fin.snoc (default : Fin 0 → ℕ) a) (b := b))

  -- Helper: compute the `pairRelabel`-pulled valuation as `![a,b,n]`.
  have hPairVal (a b : ℕ) :
      (Sum.elim (![n, i, v] : Fin 3 → ℕ) (![a, b] : Fin 2 → ℕ) ∘ pairRelabel) = ![a, b, n] := by
    funext j
    fin_cases j <;> simp [pairRelabel]

  constructor
  · intro h
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) betaGraph ![n, i, v]
          (default : Fin 0 → ℕ) :=
      (h0).1 h
    rcases (by simpa [betaGraph] using h') with ⟨a, b, hab⟩
    have hPairBody : pairBody.Realize ![n, i, v] ![a, b] := by
      simpa [hSnoc2 a b] using hab.1
    have hModBody : modBody.Realize ![n, i, v] ![a, b] := by
      simpa [hSnoc2 a b] using hab.2
    have hPair' : Nat.pair a b = n := by
      have hPairVal' : pairGraph.Realize ![a, b, n] := by
        -- `pairBody` reduces to `pairGraph` under the relabeling.
        have : pairBody.Realize ![n, i, v] ![a, b] := hPairBody
        -- Unfold and simplify the relabeling semantics.
        have : pairGraph.Realize (Sum.elim (![n, i, v] : Fin 3 → ℕ) (![a, b] : Fin 2 → ℕ) ∘ pairRelabel) :=
          (by simpa [pairBody] using this)
        simpa [hPairVal a b] using this
      exact (pairGraph_realize a b n).1 hPairVal'

    -- From `modBody` get the division witness, hence the remainder equation.
    rcases
        (bdModPos_realize (α := Fin 3) (n := 2) aVar modulus vVar (![n, i, v] : Fin 3 → ℕ)
              (![a, b] : Fin 2 → ℕ)).1 (by simpa [modBody] using hModBody) with
      ⟨q, hEq, hvLt⟩
    have hEq' : a = q * ((i + 1) * b + 1) + v := by
      simpa [aVar, iVar, vVar, bVar, modulus, addTerm, mulTerm, succTerm, numeralTerm_realize] using hEq
    have hvLt' : v < (i + 1) * b + 1 := by
      simpa [iVar, vVar, bVar, modulus, addTerm, mulTerm, succTerm, numeralTerm_realize] using hvLt
    have hModEq : a % ((i + 1) * b + 1) = v := by
      -- Use the division algorithm witness `a = q*m + v` together with `v < m`.
      have hvMod : v % ((i + 1) * b + 1) = v := Nat.mod_eq_of_lt hvLt'
      calc
        a % ((i + 1) * b + 1) = (q * ((i + 1) * b + 1) + v) % ((i + 1) * b + 1) := by
          simp [hEq']
        _ = (v + ((i + 1) * b + 1) * q) % ((i + 1) * b + 1) := by
          simp [Nat.add_comm, Nat.mul_comm]
        _ = v % ((i + 1) * b + 1) := by
          simp [Nat.add_mul_mod_self_left]
        _ = v := hvMod

    -- Rewrite `betaFun` using the witness pair `(a,b)` for `n.unpair`.
    have hunpair : n.unpair = (a, b) := by
      -- Recover `n.unpair = (a,b)` from the witness equation `Nat.pair a b = n`.
      simpa [hPair'] using (Nat.unpair_pair a b)
    have : betaFun n i = a % ((i + 1) * b + 1) := by
      simp [betaFun, hunpair]
    simp [this, hModEq]
  · intro hBeta
    -- Choose `a b` as the `unpair` of `n`.
    let a : ℕ := n.unpair.1
    let b : ℕ := n.unpair.2
    have hPair' : Nat.pair a b = n := by
      simp [a, b]
    have hmPos : 0 < ((i + 1) * b + 1) := Nat.succ_pos _
    have hR : a % ((i + 1) * b + 1) = v := by
      simpa [betaFun, a, b] using hBeta
    -- Use the quotient/remainder from `Nat.div`/`Nat.mod` to satisfy `bdModPos`.
    have hvLt : v < (i + 1) * b + 1 := by
      simpa [hR] using (Nat.mod_lt a hmPos)
    have hDivAdd : (a / ((i + 1) * b + 1)) * ((i + 1) * b + 1) + a % ((i + 1) * b + 1) = a := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod a ((i + 1) * b + 1))

    -- Rebuild `betaGraph.Realize` and discharge the two conjuncts.
    have h' :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) betaGraph ![n, i, v]
          (default : Fin 0 → ℕ) := by
      simp [betaGraph]
      refine ⟨a, b, ?_⟩
      refine And.intro ?_ ?_
      · -- `pairBody`
        have : pairGraph.Realize ![a, b, n] := (pairGraph_realize a b n).2 hPair'
        have : pairBody.Realize ![n, i, v] ![a, b] := by
          simpa [pairBody, hPairVal a b] using this
        simpa [hSnoc2 a b] using this
      · -- `modBody`
        have hMod : modBody.Realize ![n, i, v] ![a, b] := by
          -- Use `bdModPos_realize` to avoid unfolding the internal lifting machinery.
          have hEq : a = (a / ((i + 1) * b + 1)) * ((i + 1) * b + 1) + v := by
            -- `Nat.div_add_mod` gives `m * (a / m) + a % m = a`; commute and rewrite the remainder.
            have : (a / ((i + 1) * b + 1)) * ((i + 1) * b + 1) + a % ((i + 1) * b + 1) = a := by
              simpa [Nat.mul_comm] using (Nat.div_add_mod a ((i + 1) * b + 1))
            have : a = (a / ((i + 1) * b + 1)) * ((i + 1) * b + 1) + a % ((i + 1) * b + 1) := by
              simpa using this.symm
            simpa [hR] using this
          have : (bdModPos (α := Fin 3) (n := 2) aVar modulus vVar).Realize (![n, i, v] : Fin 3 → ℕ)
              (![a, b] : Fin 2 → ℕ) := by
            refine (bdModPos_realize (α := Fin 3) (n := 2) aVar modulus vVar (![n, i, v] : Fin 3 → ℕ)
                  (![a, b] : Fin 2 → ℕ)).2 ?_
            refine ⟨a / ((i + 1) * b + 1), ?_, ?_⟩
            · simpa [aVar, iVar, vVar, bVar, modulus, addTerm, mulTerm, succTerm, numeralTerm_realize] using hEq
            · simpa [iVar, vVar, bVar, modulus, addTerm, mulTerm, succTerm, numeralTerm_realize] using hvLt
          simpa [modBody] using this
        simpa [hSnoc2 a b] using hMod
    exact (h0).2 h'

end Pure

end Arithmetic

end RevHalt
