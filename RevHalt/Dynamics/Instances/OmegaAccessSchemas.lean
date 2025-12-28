/-
  RevHalt/Dynamics/Instances/OmegaAccessSchemas.lean

  Purpose:
  - Package the "arithmetical shape" of Ω-access statements as Σ₁ / Σ₂ schemas.
  - Keep it purely structural: no new oracle assumptions, no "superdecider" talk.
  - Expose: CutGe is Σ₁, WinTruth is Σ₂, and arithmetic properties on the prefix
    (e.g. Mersenne / Mersenne prime) stay PA-level inside the Σ₂ matrix.

  Dependencies:
  - OmegaChaitin staged semantics (OmegaApprox, OmegaSentence)
  - OmegaTruth limit semantics (WinTruth, OmegaTruth, prenex lemmas, StableWindowHas_prenex)
-/

import RevHalt.Dynamics.Instances.OmegaTruth

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum

namespace RevHalt.Dynamics.Instances.OmegaChaitin
namespace AccessSchemas

open LimitSemantics

/-! ## Generic arithmetical schemas (Σ₁ / Σ₂) -/

/-- Σ₁ schema for a proposition: `P ↔ ∃t, R t` with decidable matrix. -/
structure Sigma1Prop (P : Prop) where
  R : ℕ → Prop
  decR : ∀ t, Decidable (R t)
  spec : P ↔ ∃ t, R t

/-- Σ₂ schema for a proposition: `P ↔ ∃k ∃t ∀s, M k t s` with decidable matrix. -/
structure Sigma2Prop (P : Prop) where
  M : ℤ → ℕ → ℕ → Prop
  decM : ∀ k t s, Decidable (M k t s)
  spec : P ↔ ∃ k : ℤ, ∃ t : ℕ, ∀ s : ℕ, M k t s

/-! ## CutGe is Σ₁ -/

/-- `OmegaTruth (CutGe q)` is Σ₁ with witness `t ↦ (OmegaApprox t ≥ q)`. -/
def CutGe_is_sigma1 (q : ℚ) :
    Sigma1Prop (OmegaTruth (OmegaSentence.CutGe q)) where
  R := fun t => OmegaApprox t ≥ q
  decR := fun t => inferInstance
  spec := by simp only [OmegaTruth]

/-! ## WinTruth is Σ₂ (prenex ∃∃∀) -/

/-- The Σ₂ matrix used for WinTruth (this is the "arithmetical core"). -/
def WinMatrix (n : ℕ) (a : Fin 2) (k : ℤ) (t s : ℕ) : Prop :=
  R t n k ∧ ¬ R s n (k + 1) ∧ (k.toNat % 2 = (a : ℕ))

instance winMatrix_decidable (n : ℕ) (a : Fin 2) (k : ℤ) (t s : ℕ) :
    Decidable (WinMatrix n a k t s) := by
  unfold WinMatrix
  infer_instance

/-- `WinTruth n a` is Σ₂, via the prenex lemma already proved in OmegaTruth. -/
def WinTruth_is_sigma2 (n : ℕ) (a : Fin 2) :
    Sigma2Prop (WinTruth n a) where
  M := WinMatrix n a
  decM := fun k t s => inferInstance
  spec := by simpa only [WinMatrix] using (WinTruth_prenex_sigma2 n a)

/-! ## Any PA property on the prefix sits inside Σ₂ (examples: Mersenne, prime) -/

/-- Mersenne number (Nat): k+1 is a power of two. -/
def IsMersenneNat' (k : ℕ) : Prop :=
  ∃ m : ℕ, k + 1 = 2 ^ m

/-- Mersenne prime (Nat): Mersenne and prime. -/
def IsMersennePrimeNat' (k : ℕ) : Prop :=
  IsMersenneNat' k ∧ Nat.Prime k

/-- m ≤ 2^m for all m. -/
private lemma le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    calc n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (Nat.one_le_two_pow) (2 ^ n)
      _ = 2 ^ (n + 1) := by ring

/-- Decidability of IsMersenneNat' via bounded search (m ≤ k+1 suffices). -/
instance isMersenneNat'_decidable (k : ℕ) : Decidable (IsMersenneNat' k) :=
  decidable_of_iff (∃ m ≤ k + 1, k + 1 = 2 ^ m)
    ⟨fun ⟨m, _, h⟩ => ⟨m, h⟩,
     fun ⟨m, h⟩ => ⟨m, by rw [h]; exact le_two_pow m, h⟩⟩

/-- Decidability of IsMersennePrimeNat'. -/
instance isMersennePrimeNat'_decidable (k : ℕ) : Decidable (IsMersennePrimeNat' k) := by
  unfold IsMersennePrimeNat'
  infer_instance

/-- "At depth n, the stabilized prefix integer (as Nat) is Mersenne prime".
    This is *pure arithmetic on k* gated by the access barrier. -/
def OmegaPrefixIsMersennePrime' (n : ℕ) : Prop :=
  StableWindowHas n (fun k : ℤ => IsMersennePrimeNat' k.toNat)

/-- Σ₂ prenex for "prefix is Mersenne prime". -/
theorem OmegaPrefixIsMersennePrime'_prenex (n : ℕ) :
    OmegaPrefixIsMersennePrime' n ↔
      ∃ k : ℤ, ∃ t : ℕ, ∀ s : ℕ,
        R t n k ∧ ¬ R s n (k + 1) ∧ IsMersennePrimeNat' k.toNat := by
  unfold OmegaPrefixIsMersennePrime'
  simpa using (StableWindowHas_prenex n (fun k : ℤ => IsMersennePrimeNat' k.toNat))

/-- Package "prefix is Mersenne prime" as a Σ₂ schema object (matrix = access core ∧ arithmetic core). -/
def OmegaPrefixIsMersennePrime'_is_sigma2 (n : ℕ) :
    Sigma2Prop (OmegaPrefixIsMersennePrime' n) where
  M := fun k t s => R t n k ∧ ¬ R s n (k + 1) ∧ IsMersennePrimeNat' k.toNat
  decM := fun k t s => inferInstance
  spec := by simpa using (OmegaPrefixIsMersennePrime'_prenex n)

end AccessSchemas
end RevHalt.Dynamics.Instances.OmegaChaitin
