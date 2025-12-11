import Mathlib.Data.Nat.Basic

/-!
# Profiles: Abstract Cut/Bit Classification Layer

This file defines a **purely abstract** profiling vocabulary for classifying
computational objects along two orthogonal axes:

* **Cut axis** (Gödel/consistency-style): decidability of membership in cuts
* **Bit axis** (Ω/bits-style): compressibility of bit representations

This module is **agnostic** to any specific computational model (Ω, K, etc.).
It only defines the classification vocabulary. Concrete connections to Ω and
Kolmogorov complexity are made in `ProfilesOmega.lean`.

## Main Definitions

* `CutRank` : {local, ilm}
* `BitRank` : {local, transcend}
* `NumberKind` : 4-way classification (intLike, irrationalLike, transcendLike, omegaLike)
* `NumberProfile` : complete profile with kind, ranks, and delta-bands
* `InterferenceForm` : algebraic combination shapes (max+, min+, ++, +max)
-/

namespace Profiles

/-! ## 1. Axes: Cut vs Bit -/

/-- Coarse rank on the Cut axis (Gödel/consistency-style).
- `local`: finitary / locally decidable
- `ilm`: interleaved / limit behaviour, needs infinite approximation
-/
inductive CutRank
  | local
  | ilm
  deriving Repr, DecidableEq

/-- Coarse rank on the Bit axis (Ω/bits-style).
- `local`: bits are locally decidable / compressible
- `transcend`: bits are algorithmically random / incompressible
-/
inductive BitRank
  | local
  | transcend
  deriving Repr, DecidableEq

/-! ## 2. Four canonical number kinds (2×2 grid) -/

/--
Abstract 4-way classification where each kind is a point in the
(CutRank × BitRank) grid. This is agnostic to concrete objects.
-/
inductive NumberKind
  | intLike        -- (local, local)
  | irrationalLike -- (ilm, local)
  | transcendLike  -- (local, transcend)
  | omegaLike      -- (ilm, transcend)
  deriving Repr, DecidableEq

/--
A static profile combining kind, ranks, and delta-bands.
The `deltaCut`/`deltaBit` fields encode qualitative bands (0 = easy, 1 = hard).
-/
structure NumberProfile where
  kind     : NumberKind
  cutRank  : CutRank
  bitRank  : BitRank
  deltaCut : ℕ
  deltaBit : ℕ
  deriving Repr

/-! ## 3. Canonical profiles for each kind -/

def intLikeProfile : NumberProfile :=
  { kind := .intLike, cutRank := .local, bitRank := .local, deltaCut := 0, deltaBit := 0 }

def irrationalLikeProfile : NumberProfile :=
  { kind := .irrationalLike, cutRank := .ilm, bitRank := .local, deltaCut := 1, deltaBit := 0 }

def transcendLikeProfile : NumberProfile :=
  { kind := .transcendLike, cutRank := .local, bitRank := .transcend, deltaCut := 0, deltaBit := 1 }

def omegaLikeProfile : NumberProfile :=
  { kind := .omegaLike, cutRank := .ilm, bitRank := .transcend, deltaCut := 1, deltaBit := 1 }

/-- The canonical 4-way grid as a finite family. -/
def allNumberProfiles : List NumberProfile :=
  [intLikeProfile, irrationalLikeProfile, transcendLikeProfile, omegaLikeProfile]

/-! ## 4. Interference algebra: parallel vs sequential combination -/

/-- Formal tag for the 4 interference algebra shapes. -/
inductive InterferenceForm
  | max_plus   -- (max, +)
  | min_plus   -- (min, +)
  | plus_plus  -- (+, +)
  | plus_max   -- (+, max)
  deriving Repr, DecidableEq

/-- Algebraic properties of an interference form. -/
structure InterferenceProfile where
  form : InterferenceForm
  parallelIdempotent   : Bool
  parallelCommutative  : Bool
  parallelCancellative : Bool
  sequentialIdempotent   : Bool
  sequentialCommutative  : Bool
  sequentialCancellative : Bool
  deriving Repr

def maxPlusProfile : InterferenceProfile :=
  { form := .max_plus
    parallelIdempotent := true, parallelCommutative := true, parallelCancellative := false
    sequentialIdempotent := false, sequentialCommutative := true, sequentialCancellative := false }

def minPlusProfile : InterferenceProfile :=
  { form := .min_plus
    parallelIdempotent := true, parallelCommutative := true, parallelCancellative := false
    sequentialIdempotent := false, sequentialCommutative := true, sequentialCancellative := false }

def plusPlusProfile : InterferenceProfile :=
  { form := .plus_plus
    parallelIdempotent := false, parallelCommutative := true, parallelCancellative := true
    sequentialIdempotent := false, sequentialCommutative := true, sequentialCancellative := true }

def plusMaxProfile : InterferenceProfile :=
  { form := .plus_max
    parallelIdempotent := false, parallelCommutative := true, parallelCancellative := true
    sequentialIdempotent := true, sequentialCommutative := true, sequentialCancellative := false }

/-! ## 5. Axis dependency -/

/-- High-level property living on one of the axes. -/
inductive GlobalProperty
  | cutSide
  | bitSide
  deriving Repr, DecidableEq

/-- Dependency profile for a global property. -/
structure PropertyDependency where
  prop         : GlobalProperty
  dependsOnCut : Bool
  dependsOnBit : Bool
  deriving Repr

def cutDominatedProperty : PropertyDependency :=
  { prop := .cutSide, dependsOnCut := true, dependsOnBit := false }

def bitDominatedProperty : PropertyDependency :=
  { prop := .bitSide, dependsOnCut := false, dependsOnBit := true }

/-! ## 6. Profiled wrapper -/

/-- Attach a profile to any object. -/
structure Profiled (α : Type) where
  carrier : α
  profile : NumberProfile
  deriving Repr

end Profiles
