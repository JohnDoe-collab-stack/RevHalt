import RevHalt.Theory.ArithmeticLanguagePure
import RevHalt.Theory.Arithmetization.BasicNat0
import RevHalt.Theory.Arithmetization.HaltsSigma1Pure
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# RevHalt.Theory.Arithmetization.EvalnGraphPure

This file isolates the remaining obligation for the “full arithmetization” track.

In `ArithmeticLanguage.lean`, the arithmetic language `Arithmetic.Lang` includes an extra relation
symbol `Rel.evaln`, interpreted in `ℕ` as bounded evaluation of `Nat.Partrec.Code`.

For a *pure* arithmetic development (no extra relation symbols), we need a **definable graph**
for that relation inside the pure sublanguage `Arithmetic.Pure.Lang0` (only `0,succ,+,*` and `=`).

We package this as an interface `EvalnGraph0` providing:
- a pure bounded formula `evaln` with four numeric parameters `(k, codeNat, inputNat, outputNat)`,
- a standard-model specification lemma `spec`.

From this, we build the pure halting schema `H0` and prove it arithmetizes the Σ₁ witness predicate
`HaltsSigma1` (hence it can be lifted to the ambient language via `Pure.liftSentence`).

Nothing here assumes PA/Q; it is purely about definability of the `evaln` graph in the *language*.
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open Nat.Partrec
open scoped FirstOrder

namespace Pure

private def emptyVal : Empty → ℕ := fun e => nomatch e

private def fin0Val : Fin 0 → ℕ := fun i => Fin.elim0 i

/-! ### The missing “full arithmetization” interface -/

/--
`EvalnGraph0` is the **pure arithmetic definability interface** for bounded evaluation.

`evaln` should be read as a predicate on four natural numbers:

`evaln(k, codeNat, inputNat, outputNat)`

intended to mean:

`Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat`.

The key point: `evaln` is a *formula in the pure language* (`Lang0`), not a new symbol.
-/
structure EvalnGraph0 where
  /-- Pure arithmetic graph formula for `evaln` (four numeric inputs). -/
  evaln : Lang0.BoundedFormula (Fin 2) 2
  /-- Standard-model specification of the graph formula. -/
  spec :
    ∀ k codeNat inputNat outputNat : ℕ,
      evaln.Realize ![codeNat, inputNat] ![k, outputNat] ↔
        Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode codeNat) inputNat = some outputNat

namespace EvalnGraph0

/--
Pure halting schema extracted from an `evaln`-graph definition:

`H0 e := ∃ k x, evaln(k, encodeCode e, 0, x)`.
-/
def H0 (G : EvalnGraph0) (e : Code) : Sentence0 :=
  ∃' ∃'
    (G.evaln).subst
      ![numeralTerm (α := Empty) (Nat.Partrec.Code.encodeCode e), numeralTerm (α := Empty) 0]

/--
If the `evaln` graph is definable in pure arithmetic (`EvalnGraph0`), then the induced `H0`
arithmetizes the Σ₁ witness predicate `HaltsSigma1`.

This is the precise remaining obligation for “full arithmetization”:
construct an instance of `EvalnGraph0` in the pure language.
-/
theorem arithmetizesEvaln0_H0 (G : EvalnGraph0) :
    ArithmetizesEvaln0 (H0 G) := by
  intro e
  -- Decode lemma for the code numeral.
  have hDecode : Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode e) = e := by
    simpa [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.encodeCode_eq] using
      (Denumerable.ofNat_encode (α := Code) e)
  -- Normalize the substituted free-variable valuation to `![encodeCode e, 0]`.
  have hV :
      (fun a : Fin 2 =>
          Language.Term.realize emptyVal
            (![numeralTerm (α := Empty) (Nat.Partrec.Code.encodeCode e), numeralTerm (α := Empty) 0] a)) =
        ![Nat.Partrec.Code.encodeCode e, 0] := by
    ext a
    fin_cases a <;> simp [numeralTerm_realize]

  have hSnoc0 {p : Fin 0 → ℕ} {a : ℕ} :
      Fin.snoc (α := fun _ : Fin 1 => ℕ) p a 0 = a := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 1 => ℕ) (x := a) (p := p) (n := 0))

  have hSnoc1 {p : Fin 1 → ℕ} {b : ℕ} :
      Fin.snoc (α := fun _ : Fin 2 => ℕ) p b 1 = b := by
    simpa using (Fin.snoc_last (α := fun _ : Fin 2 => ℕ) (x := b) (p := p) (n := 1))

  -- Main equivalence: decode `Truth0 (H0 G e)` as `∃ k x, evaln k e 0 = some x`.
  constructor
  · intro h
    -- Expand the sentence semantics to witnesses `k` and `x`.
    rcases (by
      simpa [EvalnGraph0.H0, H0, Truth0, FirstOrder.Language.Sentence.Realize,
        FirstOrder.Language.Formula.Realize] using h) with ⟨k, x, hkx⟩
    -- Normalize the free-variable valuation using `hV` (and avoid `default` ambiguity).
    have hkx0 :
        G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0]
          (Fin.snoc (Fin.snoc fin0Val k) x) := by
      -- `hkx` has the same proposition but with `default`-chosen valuations; rewrite them away.
      have hEmpty : (@default (Empty → ℕ) Unique.instInhabited) = emptyVal :=
        Subsingleton.elim _ _
      have hFin0 : (@default (Fin 0 → ℕ) Unique.instInhabited) = fin0Val :=
        Subsingleton.elim _ _
      -- rewrite the `Fin.snoc` base and the substituted valuation, then use `hV`.
      simpa [hEmpty, hFin0, hV] using hkx
    -- Convert the `Fin.snoc` assignment to the `![k, x]` form expected by `spec`.
    have hXs : Fin.snoc (Fin.snoc fin0Val k) x = ![k, x] := by
      ext a
      fin_cases a <;> simp [hSnoc0, hSnoc1]
    have hkx1 : G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0] ![k, x] := by
      exact
        Eq.mp
          (congrArg
            (fun xs =>
              G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0] xs)
            hXs)
          hkx0
    have hEval :
        Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode e)) 0 = some x :=
      (G.spec k (Nat.Partrec.Code.encodeCode e) 0 x).1 hkx1
    exact ⟨k, x, by simpa [hDecode] using hEval⟩
  · rintro ⟨k, x, hkx⟩
    -- Rebuild `Truth0 (H0 G e)` using the witness and the graph specification.
    have hEval :
        Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode e)) 0 = some x := by
      simpa [hDecode] using hkx
    have hkx1 : G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0] ![k, x] :=
      (G.spec k (Nat.Partrec.Code.encodeCode e) 0 x).2 hEval
    have hXs : Fin.snoc (Fin.snoc fin0Val k) x = ![k, x] := by
      ext a
      fin_cases a <;> simp [hSnoc0, hSnoc1]
    have hkx0 :
        G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0]
          (Fin.snoc (Fin.snoc fin0Val k) x) := by
      exact
        Eq.mp
          (congrArg
            (fun xs =>
              G.evaln.Realize ![Nat.Partrec.Code.encodeCode e, 0] xs)
            hXs.symm)
          hkx1
    have hkx' :
        G.evaln.Realize
            (fun a : Fin 2 =>
              Language.Term.realize emptyVal
                (![numeralTerm (α := Empty) (Nat.Partrec.Code.encodeCode e), numeralTerm (α := Empty) 0] a))
            (Fin.snoc (Fin.snoc fin0Val k) x) := by
      exact
        Eq.mp
          (congrArg
            (fun v =>
              G.evaln.Realize v (Fin.snoc (Fin.snoc fin0Val k) x))
            hV.symm)
          hkx0
    -- Close the goal by unfolding `Truth0 (H0 G e)` and providing the witnesses.
    have hEmpty : (@default (Empty → ℕ) Unique.instInhabited) = emptyVal :=
      Subsingleton.elim _ _
    have hFin0 : (@default (Fin 0 → ℕ) Unique.instInhabited) = fin0Val :=
      Subsingleton.elim _ _
    refine (by
      simp [EvalnGraph0.H0, H0, Truth0, FirstOrder.Language.Sentence.Realize,
        FirstOrder.Language.Formula.Realize, hEmpty, hFin0]
      exact ⟨k, x, hkx'⟩)

end EvalnGraph0

end Pure

end Arithmetic

end RevHalt
