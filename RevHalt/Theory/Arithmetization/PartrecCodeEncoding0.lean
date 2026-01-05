import RevHalt.Theory.Arithmetization.BasicNat0
import RevHalt.Theory.Arithmetization.NatPair0
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.PartrecCodeEncoding0

Pure-arithmetic decoding lemmas for the natural-number encoding of `Nat.Partrec.Code`.

Mathlib defines a concrete Gödel encoding `Nat.Partrec.Code.encodeCode : Code → ℕ` with a decoder
`Nat.Partrec.Code.ofNatCode : ℕ → Code` (inverse via the `Denumerable Code` instance).

For the “full arithmetization” track, we want to *talk about code structure* inside the pure
arithmetic language `Lang0` (only `0,succ,+,*` and `=`). The key is that `encodeCode` uses only:

- arithmetic on naturals,
- and `Nat.pair` as a pairing combinator.

This file provides:

- pure formulas describing the constructor tags of `encodeCode`,
- and meta-level lemmas rewriting `ofNatCode` on those tagged encodings, without unfolding
  `ofNatCode` (we use the `Denumerable` inverse law).
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder
open Nat.Partrec

namespace Pure

/-! ### Pure formulas describing the `encodeCode` tag structure -/

private def cVar1 : Lang0.Term (Fin 1 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

def isZeroCode : Lang0.Formula (Fin 1) :=
  FirstOrder.Language.Term.bdEqual cVar1 (numeralTerm (α := Fin 1 ⊕ Fin 0) 0)

def isSuccCode : Lang0.Formula (Fin 1) :=
  FirstOrder.Language.Term.bdEqual cVar1 (numeralTerm (α := Fin 1 ⊕ Fin 0) 1)

def isLeftCode : Lang0.Formula (Fin 1) :=
  FirstOrder.Language.Term.bdEqual cVar1 (numeralTerm (α := Fin 1 ⊕ Fin 0) 2)

def isRightCode : Lang0.Formula (Fin 1) :=
  FirstOrder.Language.Term.bdEqual cVar1 (numeralTerm (α := Fin 1 ⊕ Fin 0) 3)

@[simp] theorem isZeroCode_realize (n : ℕ) :
    isZeroCode.Realize ![n] ↔ n = 0 := by
  have h0 :
      isZeroCode.Realize ![n] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) isZeroCode ![n] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := isZeroCode) (x := ![n]) (y := (default : Fin 0 → ℕ))).symm
  simpa [isZeroCode, cVar1] using h0

@[simp] theorem isSuccCode_realize (n : ℕ) :
    isSuccCode.Realize ![n] ↔ n = 1 := by
  have h0 :
      isSuccCode.Realize ![n] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) isSuccCode ![n] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := isSuccCode) (x := ![n]) (y := (default : Fin 0 → ℕ))).symm
  simpa [isSuccCode, cVar1] using h0

@[simp] theorem isLeftCode_realize (n : ℕ) :
    isLeftCode.Realize ![n] ↔ n = 2 := by
  have h0 :
      isLeftCode.Realize ![n] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) isLeftCode ![n] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := isLeftCode) (x := ![n]) (y := (default : Fin 0 → ℕ))).symm
  simpa [isLeftCode, cVar1] using h0

@[simp] theorem isRightCode_realize (n : ℕ) :
    isRightCode.Realize ![n] ↔ n = 3 := by
  have h0 :
      isRightCode.Realize ![n] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) isRightCode ![n] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := isRightCode) (x := ![n]) (y := (default : Fin 0 → ℕ))).symm
  simpa [isRightCode, cVar1] using h0

private def pairRelabel : Fin 3 → Fin 3 ⊕ Fin 1 :=
  ![Sum.inl 1, Sum.inl 2, Sum.inr 0]

private def pairBody : Lang0.BoundedFormula (Fin 3) 1 :=
  (show Lang0.BoundedFormula (Fin 3) 0 from pairGraph).relabel pairRelabel

private def tagEq (tag : ℕ) : Lang0.BoundedFormula (Fin 3) 1 :=
  let code : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inl 0)
  let p : Lang0.Term (Fin 3 ⊕ Fin 1) := FirstOrder.Language.Term.var (Sum.inr 0)
  FirstOrder.Language.Term.bdEqual code
    (addTerm
      (mulTerm (numeralTerm (α := Fin 3 ⊕ Fin 1) 4) p)
      (numeralTerm (α := Fin 3 ⊕ Fin 1) tag))

/--
`pairCodeGraph(n,a,b)` holds iff `n = encodeCode (Code.pair (ofNatCode a) (ofNatCode b))`.

Equivalently (and purely arithmetically): `n = 4 * Nat.pair a b + 4`.
-/
def pairCodeGraph : Lang0.Formula (Fin 3) :=
  ∃' (pairBody ⊓ tagEq 4)

/-- `compCodeGraph(n,a,b)` corresponds to the `comp` constructor tag. -/
def compCodeGraph : Lang0.Formula (Fin 3) :=
  ∃' (pairBody ⊓ tagEq 6)

/-- `precCodeGraph(n,a,b)` corresponds to the `prec` constructor tag. -/
def precCodeGraph : Lang0.Formula (Fin 3) :=
  ∃' (pairBody ⊓ tagEq 5)

private def cVar2 : Lang0.Term (Fin 2 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 0)

private def cfVar2 : Lang0.Term (Fin 2 ⊕ Fin 0) :=
  FirstOrder.Language.Term.var (Sum.inl 1)

/-- `rfindCodeGraph(n,a)` corresponds to the `rfind'` constructor tag. -/
def rfindCodeGraph : Lang0.Formula (Fin 2) :=
  FirstOrder.Language.Term.bdEqual cVar2
    (addTerm
      (mulTerm (numeralTerm (α := Fin 2 ⊕ Fin 0) 4) cfVar2)
      (numeralTerm (α := Fin 2 ⊕ Fin 0) 7))

theorem pairCodeGraph_realize (n a b : ℕ) :
    pairCodeGraph.Realize ![n, a, b] ↔ n = 4 * Nat.pair a b + 4 := by
  -- Expand the existential witness `p` and interpret `pairBody` via `pairGraph_realize`.
  have hPairVal (p : ℕ) :
      (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) = ![a, b, p] := by
    funext j
    fin_cases j <;> simp [pairRelabel]
  constructor
  · intro h
    -- Switch to `BoundedFormula.Realize` to unfold `∃'`.
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := pairCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).1 h
    rcases (by simpa [pairCodeGraph] using h0) with ⟨p, hp⟩
    have hPair : Nat.pair a b = p := by
      have : pairBody.Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.1
      have : pairGraph.Realize (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) :=
        (by simpa [pairBody] using this)
      have : pairGraph.Realize ![a, b, p] := by
        simpa [hPairVal p] using this
      exact (pairGraph_realize a b p).1 this
    have hTag : n = 4 * p + 4 := by
      have : (tagEq 4).Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.2
      simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using this
    simpa [hPair] using hTag
  · intro h
    -- Pick the witness `p := Nat.pair a b`.
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) pairCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      refine (by
        simp [pairCodeGraph]
        refine ⟨Nat.pair a b, ?_⟩
        constructor
        · -- `pairBody`
          have : pairGraph.Realize ![a, b, Nat.pair a b] := (pairGraph_realize a b (Nat.pair a b)).2 rfl
          have : pairBody.Realize (![n, a, b] : Fin 3 → ℕ) (![Nat.pair a b] : Fin 1 → ℕ) := by
            simpa [pairBody, hPairVal (Nat.pair a b)] using this
          exact this
        · -- `tagEq`
          simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using h)
    exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
      (φ := pairCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).2 h0

theorem compCodeGraph_realize (n a b : ℕ) :
    compCodeGraph.Realize ![n, a, b] ↔ n = 4 * Nat.pair a b + 6 := by
  -- Same proof as `pairCodeGraph_realize`, with tag `6`.
  have hPairVal (p : ℕ) :
      (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) = ![a, b, p] := by
    funext j
    fin_cases j <;> simp [pairRelabel]
  constructor
  · intro h
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) compCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := compCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).1 h
    rcases (by simpa [compCodeGraph] using h0) with ⟨p, hp⟩
    have hPair : Nat.pair a b = p := by
      have : pairBody.Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.1
      have : pairGraph.Realize (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) :=
        (by simpa [pairBody] using this)
      have : pairGraph.Realize ![a, b, p] := by
        simpa [hPairVal p] using this
      exact (pairGraph_realize a b p).1 this
    have hTag : n = 4 * p + 6 := by
      have : (tagEq 6).Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.2
      simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using this
    simpa [hPair] using hTag
  · intro h
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) compCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      refine (by
        simp [compCodeGraph]
        refine ⟨Nat.pair a b, ?_⟩
        constructor
        · have : pairGraph.Realize ![a, b, Nat.pair a b] := (pairGraph_realize a b (Nat.pair a b)).2 rfl
          simpa [pairBody, hPairVal (Nat.pair a b)] using this
        · simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using h)
    exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
      (φ := compCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).2 h0

theorem precCodeGraph_realize (n a b : ℕ) :
    precCodeGraph.Realize ![n, a, b] ↔ n = 4 * Nat.pair a b + 5 := by
  -- Same proof as `pairCodeGraph_realize`, with tag `5`.
  have hPairVal (p : ℕ) :
      (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) = ![a, b, p] := by
    funext j
    fin_cases j <;> simp [pairRelabel]
  constructor
  · intro h
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) precCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := precCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).1 h
    rcases (by simpa [precCodeGraph] using h0) with ⟨p, hp⟩
    have hPair : Nat.pair a b = p := by
      have : pairBody.Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.1
      have : pairGraph.Realize (Sum.elim (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) ∘ pairRelabel) :=
        (by simpa [pairBody] using this)
      have : pairGraph.Realize ![a, b, p] := by
        simpa [hPairVal p] using this
      exact (pairGraph_realize a b p).1 this
    have hTag : n = 4 * p + 5 := by
      have : (tagEq 5).Realize (![n, a, b] : Fin 3 → ℕ) (![p] : Fin 1 → ℕ) := hp.2
      simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using this
    simpa [hPair] using hTag
  · intro h
    have h0 :
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) precCodeGraph ![n, a, b]
          (default : Fin 0 → ℕ) := by
      refine (by
        simp [precCodeGraph]
        refine ⟨Nat.pair a b, ?_⟩
        constructor
        · have : pairGraph.Realize ![a, b, Nat.pair a b] := (pairGraph_realize a b (Nat.pair a b)).2 rfl
          simpa [pairBody, hPairVal (Nat.pair a b)] using this
        · simpa [tagEq, addTerm, mulTerm, numeralTerm_realize] using h)
    exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
      (φ := precCodeGraph) (x := ![n, a, b]) (y := (default : Fin 0 → ℕ))).2 h0

@[simp] theorem rfindCodeGraph_realize (n a : ℕ) :
    rfindCodeGraph.Realize ![n, a] ↔ n = 4 * a + 7 := by
  have h0 :
      rfindCodeGraph.Realize ![n, a] ↔
        FirstOrder.Language.BoundedFormula.Realize (L := Lang0) rfindCodeGraph ![n, a] (default : Fin 0 → ℕ) :=
    (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
        (φ := rfindCodeGraph) (x := ![n, a]) (y := (default : Fin 0 → ℕ))).symm
  simpa [rfindCodeGraph, cVar2, cfVar2, addTerm, mulTerm] using h0

/-! ### Meta-level `ofNatCode` rewrite lemmas for tagged encodings -/

theorem encodeCode_ofNatCode (n : ℕ) :
    Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode n) = n := by
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq] using
    (Denumerable.encode_ofNat (α := Code) n)

theorem ofNatCode_pair (a b : ℕ) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair a b + 4) =
      Nat.Partrec.Code.pair (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b) := by
  -- Compute the code whose encoding is `4 * Nat.pair a b + 4`, then use the `Denumerable` inverse law.
  have hEncA : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode a) = a :=
    encodeCode_ofNatCode a
  have hEncB : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode b) = b :=
    encodeCode_ofNatCode b
  have hEnc :
      Nat.Partrec.Code.encodeCode
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b)) =
        4 * Nat.pair a b + 4 := by
    have hMul0 (p : ℕ) : 2 * (2 * p) = 4 * p := by
      calc
        2 * (2 * p) = (2 * 2) * p := by
          simpa using (Nat.mul_assoc 2 2 p).symm
        _ = 4 * p := by simp
    simp [Nat.Partrec.Code.encodeCode, hEncA, hEncB, hMul0]
  -- Apply `ofNatCode` to both sides, using `ofNat_encode`.
  have := Denumerable.ofNat_encode
    (α := Code)
    (Nat.Partrec.Code.pair (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b))
  -- Rewrite the `Denumerable` names to `encodeCode`/`ofNatCode`.
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq, hEnc] using this

theorem ofNatCode_comp (a b : ℕ) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair a b + 6) =
      Nat.Partrec.Code.comp (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b) := by
  have hEncA : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode a) = a :=
    encodeCode_ofNatCode a
  have hEncB : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode b) = b :=
    encodeCode_ofNatCode b
  have hEnc :
      Nat.Partrec.Code.encodeCode
          (Nat.Partrec.Code.comp (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b)) =
        4 * Nat.pair a b + 6 := by
    have hMul0 (p : ℕ) : 2 * (2 * p) = 4 * p := by
      calc
        2 * (2 * p) = (2 * 2) * p := by
          simpa using (Nat.mul_assoc 2 2 p).symm
        _ = 4 * p := by simp
    have hMul1 (p : ℕ) : 2 * (2 * p + 1) = 4 * p + 2 := by
      calc
        2 * (2 * p + 1) = 2 * (2 * p) + 2 * 1 := by simp [Nat.mul_add]
        _ = 4 * p + 2 := by simp [hMul0 p]
    calc
      Nat.Partrec.Code.encodeCode
          (Nat.Partrec.Code.comp (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b)) =
        2 * (2 * Nat.pair a b + 1) + 4 := by
          simp [Nat.Partrec.Code.encodeCode, hEncA, hEncB]
      _ = (4 * Nat.pair a b + 2) + 4 := by simp [hMul1]
      _ = 4 * Nat.pair a b + 6 := by
        calc
          (4 * Nat.pair a b + 2) + 4 = 4 * Nat.pair a b + (2 + 4) := by
            simp [Nat.add_assoc]
          _ = 4 * Nat.pair a b + 6 := by simp
  have :=
    Denumerable.ofNat_encode
      (α := Code)
      (Nat.Partrec.Code.comp (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b))
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq, hEnc] using this

theorem ofNatCode_prec (a b : ℕ) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair a b + 5) =
      Nat.Partrec.Code.prec (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b) := by
  have hEncA : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode a) = a :=
    encodeCode_ofNatCode a
  have hEncB : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode b) = b :=
    encodeCode_ofNatCode b
  have hEnc :
      Nat.Partrec.Code.encodeCode
          (Nat.Partrec.Code.prec (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b)) =
        4 * Nat.pair a b + 5 := by
    have hMul0 (p : ℕ) : 2 * (2 * p) = 4 * p := by
      calc
        2 * (2 * p) = (2 * 2) * p := by
          simpa using (Nat.mul_assoc 2 2 p).symm
        _ = 4 * p := by simp
    simp [Nat.Partrec.Code.encodeCode, hEncA, hEncB, hMul0, Nat.add_assoc]
  have :=
    Denumerable.ofNat_encode
      (α := Code)
      (Nat.Partrec.Code.prec (Nat.Partrec.Code.ofNatCode a) (Nat.Partrec.Code.ofNatCode b))
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq, hEnc] using this

theorem ofNatCode_rfind (a : ℕ) :
    Nat.Partrec.Code.ofNatCode (4 * a + 7) =
      Nat.Partrec.Code.rfind' (Nat.Partrec.Code.ofNatCode a) := by
  have hEncA : Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.ofNatCode a) = a :=
    encodeCode_ofNatCode a
  have hEnc :
      Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.rfind' (Nat.Partrec.Code.ofNatCode a)) =
        4 * a + 7 := by
    have hMul0 (p : ℕ) : 2 * (2 * p) = 4 * p := by
      calc
        2 * (2 * p) = (2 * 2) * p := by
          simpa using (Nat.mul_assoc 2 2 p).symm
        _ = 4 * p := by simp
    have hMul1 (p : ℕ) : 2 * (2 * p + 1) = 4 * p + 2 := by
      calc
        2 * (2 * p + 1) = 2 * (2 * p) + 2 * 1 := by simp [Nat.mul_add]
        _ = 4 * p + 2 := by simp [hMul0 p]
    calc
      Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.rfind' (Nat.Partrec.Code.ofNatCode a)) =
        (2 * (2 * a + 1) + 1) + 4 := by
          simp [Nat.Partrec.Code.encodeCode, hEncA]
      _ = 2 * (2 * a + 1) + (1 + 4) := by
          simp [Nat.add_assoc]
      _ = 2 * (2 * a + 1) + 5 := by simp
      _ = (4 * a + 2) + 5 := by simp [hMul1]
      _ = 4 * a + 7 := by
        calc
          (4 * a + 2) + 5 = 4 * a + (2 + 5) := by
            simp [Nat.add_assoc]
          _ = 4 * a + 7 := by simp
  have :=
    Denumerable.ofNat_encode (α := Code) (Nat.Partrec.Code.rfind' (Nat.Partrec.Code.ofNatCode a))
  simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq, hEnc] using this

end Pure

end Arithmetic

end RevHalt
