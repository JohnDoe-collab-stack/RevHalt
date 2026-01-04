import Mathlib.Computability.Halting

/-!
# RevHalt.Theory.REPredExtras

Small helpers about `Nat.Partrec.REPred` that are convenient in the Gödel track.

Mathlib defines `REPred p` as “`p` is the domain of a computable partial function”. In practice,
one frequently needs closure properties such as:

> if `f : α → ℕ → Bool` is computable, then `a ↦ ∃ n, f a n = true` is r.e.

This file provides that lemma in a form directly usable to build r.e. provability predicates
from a computable proof-checker.
-/

namespace RevHalt

open Nat.Partrec

/--
If a boolean relation `f : α → ℕ → Bool` is computable, then
`fun a => ∃ n, f a n = true` is r.e. (`REPred`).

Implementation: search for a witness using `Nat.rfindOpt`.
-/
theorem rePred_exists_nat_of_computable {α : Type*} [Primcodable α]
    (f : α → ℕ → Bool) (hf : Computable₂ f) :
    REPred (fun a : α => ∃ n, f a n = true) := by
  -- Turn the predicate into an option-valued function, so that `rfindOpt` can search for a witness.
  let g : α → ℕ → Option ℕ :=
    fun a n => cond (f a n) (some n) none

  have hg : Computable₂ g := by
    -- `Computable₂` is `Computable` on pairs.
    refine Computable₂.mk ?_
    -- Build a computable function on `(a,n)` using `cond`.
    refine
      Computable.cond
        (hc := hf)
        (hf := (Computable.option_some.comp Computable.snd))
        (hg := Computable.const (α := α × ℕ) (none : Option ℕ))

  have hPartrec : Partrec fun a : α => Nat.rfindOpt (g a) := Partrec.rfindOpt hg
  have hRe : REPred fun a : α => (Nat.rfindOpt (g a)).Dom := Partrec.dom_re hPartrec

  -- Identify the domain of `rfindOpt` with the intended existential.
  refine REPred.of_eq hRe ?_
  intro a
  constructor
  · intro hDom
    rcases (Nat.rfindOpt_dom (f := g a)).1 hDom with ⟨n, _u, hu⟩
    -- `g a n = some _` forces `f a n = true`.
    have : f a n = true := by
      cases hfa : f a n with
      | false =>
          have hu' : g a n = some _u := by
            simpa [Option.mem_def] using hu
          have : False := by
            have hu'' := hu'
            simp [g, hfa] at hu''
          exact False.elim this
      | true =>
          rfl
    exact ⟨n, this⟩
  · rintro ⟨n, hn⟩
    -- Provide a witness for `rfindOpt_dom`.
    refine (Nat.rfindOpt_dom (f := g a)).2 ?_
    refine ⟨n, n, ?_⟩
    -- Membership in `Option` is definitional equality to `some`.
    simp [g, hn]

end RevHalt
