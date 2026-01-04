import RevHalt.Theory.RECodePred
import Mathlib.Computability.Halting

/-!
# RevHalt.Theory.RECodePredExtras

This file provides small “glue” lemmas connecting:

- mathlib’s `REPred` (recursively enumerable predicates over a `Primcodable` type),
- RevHalt’s `RECodePred` (the same idea, specialized to `Nat.Partrec.Code` with an explicit semi-decider).

These helpers are used in the Gödel track: once you have
`REPred Provable` and a (computable) arithmetization map `Code → Sentence`, you can package the
required r.e. hypothesis `RECodePred (fun c => Provable (… c …))` automatically.
-/

namespace RevHalt

open Nat.Partrec

namespace RECodePred

/--
If `P` is r.e. on some `Primcodable` type `α`, then for any computable map `g : Code → α`,
the predicate `fun c => P (g c)` is r.e. as a `RECodePred`.
-/
def of_REPred_comp {α : Type*} [Primcodable α]
    {P : α → Prop} (hP : REPred P)
    (g : Code → α) (hg : Computable g) :
    RECodePred (fun c => P (g c)) := by
  -- A semi-decider returning `0` when `P (g c)` holds (and diverging otherwise).
  let f : Code → (Nat →. Nat) :=
    fun c =>
      fun _ =>
        (Part.assert (P (g c)) fun _ => Part.some (PUnit.unit)).map (fun _ : PUnit => (0 : Nat))

  refine ⟨f, ?_, ?_⟩

  · -- `f` is partial recursive (uniformly in `(c, n)`), since it is obtained by composing the
    -- `REPred` witness with a computable map and then ignoring the second argument.
    unfold Partrec₂
    -- Start from the canonical partial recursive witness of `REPred P`.
    have hAssert : Partrec fun a : α =>
        Part.assert (P a) fun _ => Part.some (PUnit.unit) := hP
    -- Map the witness value to a dummy natural (`0`).
    have hMapConst : Computable₂ (fun (_a : α) (_u : PUnit) => (0 : Nat)) :=
      (Computable.to₂ (Computable.const (α := α × PUnit) (0 : Nat)))
    have hNat : Partrec fun a : α =>
        (Part.assert (P a) fun _ => Part.some (PUnit.unit)).map (fun _ : PUnit => (0 : Nat)) :=
      Partrec.map hAssert hMapConst
    -- Compose with `g : Code → α`.
    have hCode : Partrec fun c : Code =>
        (Part.assert (P (g c)) fun _ => Part.some (PUnit.unit)).map (fun _ : PUnit => (0 : Nat)) :=
      hNat.comp hg
    -- Ignore the second argument by composing with `Prod.fst`.
    have hPair : Partrec fun p : Code × Nat =>
        (Part.assert (P (g p.1)) fun _ => Part.some (PUnit.unit)).map (fun _ : PUnit => (0 : Nat)) :=
      hCode.comp Computable.fst
    -- This is exactly `Partrec₂ f`.
    simpa [f] using hPair

  · intro c
    -- `f c 0` is defined iff `P (g c)` holds.
    have hDom : (f c 0).Dom ↔ P (g c) := by
      constructor
      · intro h
        -- Unfold `f` and the `Part.map` domain.
        dsimp [f] at h
        rcases h with ⟨hPgc, _⟩
        exact hPgc
      · intro hPgc
        -- Provide the witness for `Part.assert`.
        refine ⟨hPgc, ?_⟩
        trivial

    -- Convert domain to existence of an output value.
    constructor
    · intro hPgc
      exact (Part.dom_iff_mem).1 ((hDom).2 hPgc)
    · intro hx
      exact (hDom).1 ((Part.dom_iff_mem).2 hx)

end RECodePred

end RevHalt
