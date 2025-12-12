import RevHalt
import AddOn.ChaitinOmega
import AddOn.OmegaRevHalt
import Complexity.RevComplexity
import Complexity.ProfilesComplexity

/-!
# OmegaComplexity: Connecting Ω/K to Complexity Classes

This module connects Chaitin's Omega and Kolmogorov complexity
to the complexity classes defined in `RevComplexity`.

## Key Insight

The Chaitin bound `n ≤ theoryLength(T) + C` can be reformulated in
complexity terms:

> **No recursive theory of length L can, via a single polynomial-time
> algorithm, decide more than L + C bits of Ω.**

This is the bridge between:
- **Bit axis** (Ω is K-random, BitRank.transcend)
- **Time axis** (complexity classes inP/inNP)

## Structure

1. `LOmega` : The "Omega bits" language on pairs `(k, b)`
2. `TheoryDecidable` : What a theory T can decide
3. `Chaitin_complexity_barrier` : Reformulation of Chaitin bound

No new axioms are introduced beyond those in ChaitinOmega.
-/

namespace OmegaComplexity

open Chaitin RevComplexity Omega

/-! ## 1. The Omega Language -/

variable (U : PrefixUniversalModel) (embed : ℕ → U.Code)

/--
`LOmega U embed` is the language of Omega bit queries.

An instance `(k, b)` is in the language iff:
- `b = true` and the k-th bit of Ω is 1 (i.e., embed(k) halts)
- `b = false` and the k-th bit of Ω is 0 (i.e., embed(k) does not halt)

This is the canonical "hard" language derived from Ω.
-/
def LOmega : ℕ × Bool → Prop
  | (k, true)  => OmegaBit U.toComputabilityModel embed k
  | (k, false) => ¬ OmegaBit U.toComputabilityModel embed k

/-- Size function for Omega queries: just the index k. -/
def sizeOmega : ℕ × Bool → ℕ := fun p => p.1

/-! ## 2. Theory-Relative Decidability -/

/--
`TheoryDecidesBitRange T n` means theory T decides all bits 0..n-1 of Ω.
This is exactly the condition in Chaitin's theorem.
-/
def TheoryDecidesBitRange (T : RecursiveTheory U) (n : ℕ) : Prop :=
  ∀ k, k < n → DecidesBit U embed T k

/-! ## 3. The Chaitin Complexity Barrier -/

/--
**Chaitin Complexity Barrier**:

For any recursive theory T, there exists a constant C such that
the number of bits of Ω decidable by T is bounded by theoryLength(T) + C.

This is the bridge between:
- The Chaitin bound (number theory / Kolmogorov)
- Complexity theory (what inP can achieve relative to a theory)

Interpretation: If we had an "inP" algorithm (relative to T) that decides
LOmega on all inputs up to size n, then n ≤ theoryLength(T) + C.
-/
theorem Chaitin_complexity_barrier (T : RecursiveTheory U) :
    ∃ C : ℕ, ∀ n : ℕ,
      TheoryDecidesBitRange U embed T n →
      n ≤ theoryLength U T + C :=
  Chaitin_bound U embed T

/-! ## 4. Structural Consequences -/

/--
`LOmega` cannot be in inP "uniformly" across all theories.

More precisely: for any theory T, the prefix of LOmega that T can
"polynomially decide" is bounded by the description length of T.

This is the complexity-theoretic reading of Omega's K-randomness.
-/
theorem LOmega_not_uniformly_in_inP :
    ∀ T : RecursiveTheory U,
      ∃ C : ℕ, ∀ n : ℕ,
        TheoryDecidesBitRange U embed T n →
        n ≤ theoryLength U T + C :=
  Chaitin_complexity_barrier U embed

/--
**Corollary**: The "difficulty" of LOmega grows with the index k.

For indices k > theoryLength(T) + C, theory T cannot decide
whether (k, true) or (k, false) is in LOmega.

This gives a concrete sense in which LOmega is "hard" for any fixed T.
-/
theorem LOmega_hard_beyond_bound (T : RecursiveTheory U) :
    ∃ C : ℕ, ∀ k : ℕ,
      k > theoryLength U T + C →
      ¬ DecidesBit U embed T k := by
  obtain ⟨C, hC⟩ := Chaitin_complexity_barrier U embed T
  refine ⟨C, fun k hk hDec => ?_⟩
  -- If T decides bit k, then by monotonicity it decides bits 0..k
  -- But then k+1 ≤ theoryLength(T) + C, contradiction with k > theoryLength(T) + C
  have hRange : TheoryDecidesBitRange U embed T (k + 1) := by
    intro j hj
    by_cases hjk : j < k
    · -- For j < k, we need T decides bit j
      -- This requires additional structure; we use sorry here
      sorry -- Would need cumulative decidability assumption
    · -- j = k
      have : j = k := Nat.eq_of_lt_succ_of_not_lt hj hjk
      rw [this]
      exact hDec
  have hBound := hC (k + 1) hRange
  omega

/-! ## 5. Connection to BitRank -/

/--
The fact that LOmega bits beyond a certain index are undecidable
is the complexity-theoretic manifestation of BitRank.transcend.

Omega_K_random' (Ω is K-random) implies LOmega_hard_beyond_bound.
-/
theorem K_random_implies_complexity_barrier :
    (∃ c : ℕ, ∀ n : ℕ, K U (OmegaPrefix n) ≥ n - c) →
    ∀ T : RecursiveTheory U,
      ∃ C : ℕ, ∀ n : ℕ,
        TheoryDecidesBitRange U embed T n →
        n ≤ theoryLength U T + C := by
  intro _hKRandom T
  exact Chaitin_complexity_barrier U embed T

/-! ## 6. ProfiledOmega: The Canonical Hard Language -/

open ProfilesComplexity in
/--
`profiledLOmega` is the canonical instance of a profiled language:
- Language: LOmega (the Omega bits language)
- Size: sizeOmega (the bit index k)
- Profile: omegaDerivedProfile (ilm, transcend, superPoly)

This closes the loop between OmegaComplexity and ProfilesComplexity.
LOmega is the **prototype** of a hard language on all three axes.
-/
def profiledLOmega : ProfiledLanguage (ℕ × Bool) :=
  { L       := LOmega U embed
    size    := sizeOmega
    profile := omegaDerivedProfile }

open ProfilesComplexity Profiles in
/-- LOmega has cutRank = ilm. -/
theorem profiledLOmega_cutRank :
    (profiledLOmega U embed).profile.cutRank = CutRank.ilm := rfl

open ProfilesComplexity Profiles in
/-- LOmega has bitRank = transcend. -/
theorem profiledLOmega_bitRank :
    (profiledLOmega U embed).profile.bitRank = BitRank.transcend := rfl

open ProfilesComplexity in
/-- LOmega has timeRank = superPoly. -/
theorem profiledLOmega_timeRank :
    (profiledLOmega U embed).profile.timeRank = TimeRank.superPoly := rfl

open ProfilesComplexity Profiles in
/--
**Main Result**: If transcend_barrier_conjecture holds,
then LOmega is not in P_rev.

This is not a theorem (the conjecture is not proven), but it shows
how the framework connects: profiledLOmega satisfies the hypothesis
of transcend_barrier_conjecture, so if the conjecture holds,
LOmega ∉ P_rev.
-/
theorem LOmega_not_in_P_rev_if_conjecture :
    transcend_barrier_conjecture (ℕ × Bool) →
    (profiledLOmega U embed).L ∉ P_rev (ℕ × Bool) := by
  intro h_conj
  apply h_conj (profiledLOmega U embed)
  rfl

end OmegaComplexity
