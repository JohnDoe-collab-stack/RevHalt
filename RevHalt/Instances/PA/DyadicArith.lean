/-
  RevHalt/Instances/PA/DyadicArith.lean

  PA-facing dyadic arithmetic scaffolding.

  What this provides (no sorries, compiles):
  - A canonical encoding of integers into ℕ (PA codes)
  - A canonical encoding of dyadics k/2^n into ℕ (PA codes)
  - A minimal Σ₁-syntax notion for your PASentence layer (via Halt constructor)

  This is deliberately minimal: it does NOT yet prove the big bridge lemmas
  (those will live in the Arithmetization layer once we connect Ω-access to PA).
-/

import RevHalt.Instances.PA.Logic
import RevHalt.Instances.PA.Encoding
import RevHalt.Instances.PA.Arithmetization

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Prime.Defs

namespace RevHalt.Instances.PA

/-! ## 1) Integer coding (ℤ ↔ ℕ) as PA codes -/

/-- Encode an integer as a natural number:
    nonneg k ↦ 2*k,  neg k ↦ 2*(-k)-1  (standard zigzag encoding). -/
def encodeInt (k : ℤ) : ℕ :=
  if 0 ≤ k then
    2 * Int.toNat k
  else
    2 * Int.toNat (-k) - 1

/-- Decode a natural number as an integer (inverse-ish of encodeInt).
    Even n ↦ n/2, odd n ↦ -((n+1)/2). -/
def decodeInt (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    Int.ofNat (n / 2)
  else
    - (Int.ofNat ((n + 1) / 2))

/-- Convenient lemma: `decodeInt` outputs a nonnegative integer on even inputs. -/
theorem decodeInt_of_even {n : ℕ} (h : n % 2 = 0) :
    0 ≤ decodeInt n := by
  unfold decodeInt
  simp only [h, ↓reduceIte]
  exact Int.natCast_nonneg _

/-- Convenient lemma: `decodeInt` outputs a negative integer on odd inputs. -/
theorem decodeInt_of_odd {n : ℕ} (h : n % 2 = 1) :
    decodeInt n < 0 := by
  unfold decodeInt
  simp only [h, Nat.one_ne_zero, ↓reduceIte, Left.neg_neg_iff]
  -- Goal: 0 < Int.ofNat ((n + 1) / 2)
  -- Simply: Int.ofNat x > 0 ↔ x > 0, and (n+1)/2 > 0 for odd n ≥ 1
  have hge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hpos : 0 < (n + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
  exact Int.natCast_pos.mpr hpos

/-! ## 2) Dyadic coding (k/2^n) as PA codes -/

/-- Dyadic descriptor (mathematical object). -/
structure Dyadic where
  k : ℤ
  n : ℕ

/-- PA code for a dyadic is just a Nat. -/
abbrev DyadicCode := ℕ

/-- Encode a dyadic (k,n) into a PA code using Nat pairing. -/
def encodeDyadic (d : Dyadic) : DyadicCode :=
  Nat.pair (encodeInt d.k) d.n

/-- Decode a dyadic PA code back into (k,n) using Nat unpairing. -/
def decodeDyadic (c : DyadicCode) : Dyadic :=
  let p := Nat.unpair c
  { k := decodeInt p.1, n := p.2 }

/-- Project the numerator integer from a dyadic code. -/
def dyadicK (c : DyadicCode) : ℤ :=
  (decodeDyadic c).k

/-- Project the exponent n from a dyadic code. -/
def dyadicN (c : DyadicCode) : ℕ :=
  (decodeDyadic c).n

/-! ## 3) Minimal Σ₁ syntax notion (PA sentences)

  You said explicitly:
  - PASentence has `Halt n` as the built-in Σ₁ constructor.
  We expose the *syntax* notion "Σ₁ sentence" as: "is (Halt n) for some n".
-/

open scoped Classical

/-- Minimal Σ₁-sentence predicate: exactly the Halt-formulas. -/
def IsSigma1Sentence (s : PASentence) : Prop :=
  ∃ n : ℕ, s = PASentence.Halt n

theorem IsSigma1Sentence.halt (n : ℕ) :
    IsSigma1Sentence (PASentence.Halt n) := by
  exact ⟨n, rfl⟩

/-- A tiny wrapper object: a Σ₁ sentence packaged with its witness. -/
structure Sigma1Sentence where
  s : PASentence
  isSigma1 : IsSigma1Sentence s

/-- Constructor: package `Halt n` as a Sigma1Sentence. -/
def Sigma1Sentence.halt (n : ℕ) : Sigma1Sentence :=
  ⟨PASentence.Halt n, IsSigma1Sentence.halt n⟩

/-! ## 4) Dyadic arithmetical primitives you will need next

  These are PA-level "number-theory" predicates on naturals,
  used later once we link Ω-prefix integer k to arithmetic properties.
-/

/-- Nat Mersenne: k+1 is a power of two. -/
def IsMersenne (k : ℕ) : Prop :=
  ∃ m : ℕ, k + 1 = 2 ^ m

/-- Nat Mersenne prime: Mersenne and prime. -/
def IsMersennePrime (k : ℕ) : Prop :=
  IsMersenne k ∧ Nat.Prime k

/-- Parity as a PA predicate (Δ₀): k mod 2 = b. -/
def HasParity (k b : ℕ) : Prop :=
  k % 2 = b

end RevHalt.Instances.PA
