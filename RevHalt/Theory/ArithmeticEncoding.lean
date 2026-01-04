import RevHalt.Theory.ArithmeticLanguage
import Mathlib.ModelTheory.Encoding

/-!
# RevHalt.Theory.ArithmeticEncoding

This file provides computability-oriented encodings for the arithmetic syntax used in the Gödel track.

It equips:
- the arithmetic function-symbol bundle `Σ i, Func i` with `Encodable`,
- arithmetic sentences `Sentence := Lang.Sentence` with `Encodable`,
- the relation-symbol bundle `Σ n, Rel n` with `Encodable`,

by reusing the list encodings from `Mathlib.ModelTheory.Encoding`.

This is a stepping stone for:
- defining r.e. (syntactic) provability predicates,
- and arithmetizing computation (`H : Code → Sentence`).
-/

namespace RevHalt

namespace Arithmetic

open FirstOrder
open scoped FirstOrder

namespace Encoding

def encodeFuncSigma : (Σ i, Lang.Functions i) → Nat
  | ⟨0, Func.zero⟩ => 0
  | ⟨1, Func.succ⟩ => 1
  | ⟨2, Func.add⟩ => 2
  | ⟨2, Func.mul⟩ => 3

def decodeFuncSigma : Nat → Option (Σ i, Lang.Functions i)
  | 0 => some ⟨0, Func.zero⟩
  | 1 => some ⟨1, Func.succ⟩
  | 2 => some ⟨2, Func.add⟩
  | 3 => some ⟨2, Func.mul⟩
  | _ => none

@[simp] theorem decodeFuncSigma_encodeFuncSigma (x : Σ i, Lang.Functions i) :
    decodeFuncSigma (encodeFuncSigma x) = some x := by
  cases x with
  | mk i f =>
    cases f <;> rfl

instance : Encodable (Σ i, Lang.Functions i) :=
  ⟨encodeFuncSigma, decodeFuncSigma, decodeFuncSigma_encodeFuncSigma⟩

def encodeRelSigma : (Σ n, Lang.Relations n) → Nat
  | ⟨4, Rel.evaln⟩ => 0

def decodeRelSigma : Nat → Option (Σ n, Lang.Relations n)
  | 0 => some ⟨4, Rel.evaln⟩
  | _ => none

@[simp] theorem decodeRelSigma_encodeRelSigma (x : Σ n, Lang.Relations n) :
    decodeRelSigma (encodeRelSigma x) = some x := by
  cases x with
  | mk _ r =>
      cases r
      rfl

instance : Encodable (Σ n, Lang.Relations n) :=
  ⟨encodeRelSigma, decodeRelSigma, decodeRelSigma_encodeRelSigma⟩

instance : Encodable (Σ n, Lang.BoundedFormula Empty n) :=
  Encodable.ofLeftInjection
    (fun φ : Σ n, Lang.BoundedFormula Empty n => φ.2.listEncode)
    (fun l => (FirstOrder.Language.BoundedFormula.listDecode (L := Lang) (α := Empty) l)[0]?)
    (fun φ => by
      have h :=
        FirstOrder.Language.BoundedFormula.listDecode_encode_list (L := Lang) (α := Empty) [φ]
      rw [List.flatMap_singleton] at h
      simpa using congrArg (fun l => l[0]?) h)

instance : Encodable Sentence :=
  Encodable.ofLeftInjection
    (fun φ : Sentence => (⟨0, φ⟩ : Σ n, Lang.BoundedFormula Empty n))
    (fun ψ =>
      match ψ with
      | ⟨0, φ⟩ => some (show Sentence from φ)
      | ⟨_ + 1, _⟩ => none)
    (fun _ => rfl)

end Encoding

end Arithmetic

end RevHalt
