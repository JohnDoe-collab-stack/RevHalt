/-
  RevHalt/Dynamics/Instances/OmegaTruth.lean

  DROP-IN MODULE: Limit semantics for the Ω instance.

  Goal:
  - Make the Σ₁ vs (Σ₁ ∧ Π₁) / Σ₂ "access barrier" explicit *as arithmetic*.
  - Keep it faithful to your existing staged semantics `OmegaSat t` (time-indexed),
    while defining a separate *limit truth* predicate `OmegaTruth`.

  Key idea:
  - `CutGe q` is Σ₁:     ∃t, OmegaApprox t ≥ q
  - `WinDyad n a` is Σ₂: ∃k, (∃t, OmegaApprox t ≥ k/2^n) ∧ (∀s, ¬(OmegaApprox s ≥ (k+1)/2^n)) ∧ parity(k)=a
  - `BitIs n a` is *defined* to have the same limit truth as `WinDyad n a` (clean "Bit = window" at truth level).

  This file does NOT assume any additional "oracle"; it only exposes the quantifier structure.
-/

import RevHalt.Dynamics.Instances.OmegaChaitin

import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace RevHalt.Dynamics.Instances.OmegaChaitin

open scoped BigOperators

/-- Arithmetic helper: parity bit as `Fin 2`. -/
def bitOfNat (k : ℕ) : Fin 2 :=
  ⟨k % 2, by
    have : 0 < (2 : ℕ) := by norm_num
    exact Nat.mod_lt k this⟩

namespace LimitSemantics

/-
  Primitive recursive/decidable core predicate.

  We keep `k : ℤ` to match your staged `WinDyad` (which quantifies over ℤ),
  and to avoid silently changing the object language.
-/

/-- `R t n k` := "at time t, Ωₜ ≥ k/2^n". Decidable (hence Δ₀ once arithmetized). -/
def R (t n : ℕ) (k : ℤ) : Prop :=
  OmegaApprox t ≥ ((k : ℚ) / (2 ^ n))

instance (t n : ℕ) (k : ℤ) : Decidable (R t n k) := by
  unfold R
  infer_instance

/-- Limit-truth for dyadic windows (the Σ₁ ∧ Π₁ / Σ₂ access barrier). -/
def WinTruth (n : ℕ) (a : Fin 2) : Prop :=
  ∃ k : ℤ,
    (∃ t : ℕ, R t n k) ∧
    (∀ s : ℕ, ¬ R s n (k + 1)) ∧
    (k.toNat % 2 = (a : ℕ))

/-- Limit truth semantics for Ω-sentences. -/
def OmegaTruth : OmegaSentence → Prop
| OmegaSentence.CutGe q => ∃ t : ℕ, OmegaApprox t ≥ q
| OmegaSentence.BitIs n a => WinTruth n a
| OmegaSentence.WinDyad n a => WinTruth n a
| OmegaSentence.Not s => ¬ OmegaTruth s
| OmegaSentence.TrueS => True
| OmegaSentence.FalseS => False

@[simp] theorem OmegaTruth_CutGe (q : ℚ) :
    OmegaTruth (OmegaSentence.CutGe q) ↔ ∃ t : ℕ, OmegaApprox t ≥ q := by
  rfl

@[simp] theorem OmegaTruth_BitIs (n : ℕ) (a : Fin 2) :
    OmegaTruth (OmegaSentence.BitIs n a) ↔ WinTruth n a := by
  rfl

@[simp] theorem OmegaTruth_WinDyad (n : ℕ) (a : Fin 2) :
    OmegaTruth (OmegaSentence.WinDyad n a) ↔ WinTruth n a := by
  rfl

/-- Bit and Win have the same *limit* truth by definition (clean separation). -/
theorem OmegaTruth_Bit_eq_Win (n : ℕ) (a : Fin 2) :
    OmegaTruth (OmegaSentence.BitIs n a) ↔ OmegaTruth (OmegaSentence.WinDyad n a) := by
  rfl

/-
  Prenex Σ₂ form: ∃k ∃t ∀s [ R(t,n,k) ∧ ¬R(s,n,k+1) ∧ parity(k)=a ].

  The "matrix" is decidable given `R` is decidable.
-/
theorem WinTruth_prenex_sigma2 (n : ℕ) (a : Fin 2) :
    WinTruth n a ↔
      ∃ k : ℤ, ∃ t : ℕ, ∀ s : ℕ,
        R t n k ∧ ¬ R s n (k + 1) ∧ (k.toNat % 2 = (a : ℕ)) := by
  constructor
  · rintro ⟨k, ⟨t, ht⟩, hs, hpar⟩
    refine ⟨k, t, ?_⟩
    intro s
    exact ⟨ht, hs s, hpar⟩
  · rintro ⟨k, t, h⟩
    have ht : R t n k := (h 0).1
    have hs : ∀ s : ℕ, ¬ R s n (k + 1) := fun s => (h s).2.1
    have hpar : k.toNat % 2 = (a : ℕ) := (h 0).2.2
    exact ⟨k, ⟨t, ht⟩, hs, hpar⟩

/-- The Π₁ "stabilization" component exposed as a strict inequality (pure arithmetic rewrite). -/
theorem access_barrier_pi1 (n : ℕ) (k : ℤ) :
    (∀ s : ℕ, ¬ R s n (k + 1)) ↔
    ∀ s : ℕ, OmegaApprox s < (((k + 1 : ℤ) : ℚ) / (2 ^ n)) := by
  simp [R, not_le]

/-
  "Arithmetization hook": any PA/primitive arithmetic property on the prefix integer k
  lives in the matrix; the *only* hard part is the Π₁ stabilization.

  We state this cleanly as a Σ₂-shape lemma for arbitrary P on ℤ (or on ℕ via toNat).
-/

/-
  ✅ Correct, tight version: bind the SAME k in WinTruth.

  This is the one you want for "arith_access_link" style statements.
-/

/-- Correct "access → arithmetic" statement: the k is shared between WinTruth and P(k). -/
def StableWindowHas (n : ℕ) (P : ℤ → Prop) : Prop :=
  ∃ k : ℤ, (∃ t : ℕ, R t n k) ∧ (∀ s : ℕ, ¬ R s n (k + 1)) ∧ (P k)

/-- Prenex Σ₂ for the correct shared-k statement. -/
theorem StableWindowHas_prenex (n : ℕ) (P : ℤ → Prop) :
    StableWindowHas n P ↔
      ∃ k : ℤ, ∃ t : ℕ, ∀ s : ℕ,
        R t n k ∧ ¬ R s n (k + 1) ∧ P k := by
  constructor
  · rintro ⟨k, ⟨t, ht⟩, hs, hP⟩
    refine ⟨k, t, ?_⟩
    intro s
    exact ⟨ht, hs s, hP⟩
  · rintro ⟨k, t, h⟩
    have ht : R t n k := (h 0).1
    have hs : ∀ s : ℕ, ¬ R s n (k + 1) := fun s => (h s).2.1
    have hP : P k := (h 0).2.2
    exact ⟨k, ⟨t, ht⟩, hs, hP⟩

/-
  Concrete arithmetic examples: Mersenne / Mersenne prime on the prefix integer.

  (These are *pure* PA properties of the integer k — the barrier lives in the WinTruth part.)
-/

/-- k is a (nonnegative) Mersenne number: k+1 is a power of two. -/
def IsMersenneNat (k : ℕ) : Prop :=
  ∃ m : ℕ, k + 1 = 2 ^ m

/-- Mersenne prime predicate (pure arithmetic on ℕ). -/
def IsMersennePrimeNat (k : ℕ) : Prop :=
  IsMersenneNat k ∧ Nat.Prime k

/-- "At depth n, the stabilized prefix integer (as Nat) is Mersenne prime" as a Σ₂-shaped statement. -/
def OmegaPrefixIsMersennePrime (n : ℕ) : Prop :=
  StableWindowHas n (fun k : ℤ => IsMersennePrimeNat k.toNat)

/-- Prenex Σ₂ form for "prefix is Mersenne prime" (shared k). -/
theorem OmegaPrefixIsMersennePrime_prenex (n : ℕ) :
    OmegaPrefixIsMersennePrime n ↔
      ∃ k : ℤ, ∃ t : ℕ, ∀ s : ℕ,
        R t n k ∧ ¬ R s n (k + 1) ∧ IsMersennePrimeNat k.toNat := by
  -- just unfold and reuse the generic prenex lemma
  unfold OmegaPrefixIsMersennePrime
  simpa using (StableWindowHas_prenex (n := n) (P := fun k : ℤ => IsMersennePrimeNat k.toNat))

end LimitSemantics

end RevHalt.Dynamics.Instances.OmegaChaitin
