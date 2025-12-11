import RevHalt
import OmegaRevHalt

/-!
# Profiles: Cut/Bit Classification Layer

This file defines a *synthetic* profiling layer on top of the core
RevHalt framework.

It does **not** add new axioms or heavy theorems. Instead it:

* formalizes the 2×2 classification grid (Cut-axis × Bit-axis),
* introduces four canonical "number kinds" (IntLike, IrrationalLike, TranscendLike, OmegaLike),
* records which Δ-layer is active on each axis,
* sketches an "interference algebra" classification for combination laws.

This module connects:
* the Δ-band (`deltaScaled`) on finite windows,
* the Ω-bits view (`Omega.OmegaBit`),
* and complexity / measure–theoretic interpretations.
-/

namespace Profiles

/-! ## 1. Axes: Cut vs Bit -/

/-- Coarse rank on the *Cut* axis (Gödel/consistency-style). -/
inductive CutRank
  | local    -- behaves in a finitary / locally decidable way
  | ilm      -- "interleaved / limit" behaviour, needs infinite approximation
  deriving Repr, DecidableEq

/-- Coarse rank on the *Bit* axis (Ω/bits-style). -/
inductive BitRank
  | local       -- bits are locally decidable
  | transcend   -- bits behave like algorithmically random / incompressible
  deriving Repr, DecidableEq

/-! ## 2. Four canonical "number kinds" (2×2 grid) -/

/--
Abstract 4-way classification where each "kind" is a point in the
(CutRank × BitRank) grid.

This is deliberately agnostic: we are not yet tying these kinds to
actual ℝ/ℚ/Ω values — only to their *profile* on the two axes.
-/
inductive NumberKind
  | intLike        -- locally tame on both Cut and Bit
  | irrationalLike -- Cut needs ilm, Bit stays local
  | transcendLike  -- Cut local, Bit transcend
  | omegaLike      -- both axes in their "hard" regime
  deriving Repr, DecidableEq

/--
A static profile combining:

* a `NumberKind`
* its rank on Cut and Bit axes
* the qualitative Δ-bands on each axis (0 or 1 in the original table).

The `deltaCut` / `deltaBit` fields encode the qualitative "band" (0, 1, or intermediate)
for each axis. We keep them as plain Naturals for now, to be refined later.
-/
structure NumberProfile where
  kind     : NumberKind
  cutRank  : CutRank
  bitRank  : BitRank
  deltaCut : ℕ
  deltaBit : ℕ
  deriving Repr

/-- IntLike line of the table. -/
def intLikeProfile : NumberProfile :=
  { kind     := .intLike
    cutRank  := .local
    bitRank  := .local
    deltaCut := 0
    deltaBit := 0 }

/-- IrrationalLike line of the table. -/
def irrationalLikeProfile : NumberProfile :=
  { kind     := .irrationalLike
    cutRank  := .ilm
    bitRank  := .local
    deltaCut := 1
    deltaBit := 0 }

/-- TranscendLike: Cut axis is local, Bit axis is transcendent. -/
def transcendLikeProfile : NumberProfile :=
  { kind     := .transcendLike
    cutRank  := .local
    bitRank  := .transcend
    deltaCut := 0
    deltaBit := 1 }

/-- OmegaLike line of the table. -/
def omegaLikeProfile : NumberProfile :=
  { kind     := .omegaLike
    cutRank  := .ilm
    bitRank  := .transcend
    deltaCut := 1
    deltaBit := 1 }

/--
The canonical 4-way grid as a finite family.
Useful for case analysis and for connecting concrete objects to profiles.
-/
def allNumberProfiles : List NumberProfile :=
  [intLikeProfile, irrationalLikeProfile, transcendLikeProfile, omegaLikeProfile]

/-! ## 3. Interference algebra: parallel vs sequential combination -/

/--
Formal tag for the 4 "interference algebra" shapes from the table:

* `max_plus` : (max, +)
* `min_plus` : (min, +)
* `plus_plus`: (+, +)
* `plus_max` : (+, max)
-/
inductive InterferenceForm
  | max_plus
  | min_plus
  | plus_plus
  | plus_max
  deriving Repr, DecidableEq

/--
Abstract classification of the algebraic behaviour of a given form.

We record, for each form:

* whether the *parallel* operator is idempotent / commutative / cancellative,
* whether the *sequential* operator is idempotent / commutative / cancellative.

This is descriptive metadata; actual algebraic structures will be
hooked in later as instances.
-/
structure InterferenceProfile where
  form : InterferenceForm
  parallelIdempotent   : Bool
  parallelCommutative  : Bool
  parallelCancellative : Bool
  sequentialIdempotent   : Bool
  sequentialCommutative  : Bool
  sequentialCancellative : Bool
  deriving Repr

/-- (max, +) row of the table. -/
def maxPlusProfile : InterferenceProfile :=
  { form := .max_plus
    parallelIdempotent   := true
    parallelCommutative  := true
    parallelCancellative := false
    sequentialIdempotent   := false
    sequentialCommutative  := true
    sequentialCancellative := false }

/-- (min, +) row of the table. -/
def minPlusProfile : InterferenceProfile :=
  { form := .min_plus
    parallelIdempotent   := true
    parallelCommutative  := true
    parallelCancellative := false
    sequentialIdempotent   := false
    sequentialCommutative  := true
    sequentialCancellative := false }

/-- (+, +) row of the table. -/
def plusPlusProfile : InterferenceProfile :=
  { form := .plus_plus
    parallelIdempotent   := false
    parallelCommutative  := true
    parallelCancellative := true
    sequentialIdempotent   := false
    sequentialCommutative  := true
    sequentialCancellative := true }

/-- (+, max) row of the table. -/
def plusMaxProfile : InterferenceProfile :=
  { form := .plus_max
    parallelIdempotent   := false
    parallelCommutative  := true
    parallelCancellative := true
    sequentialIdempotent   := true
    sequentialCommutative  := true
    sequentialCancellative := false }

/-! ## 4. Global properties and orthogonality of the axes -/

/--
Two high-level properties that live on orthogonal axes:

* `cutSide`  : properties whose behaviour is controlled by the Cut axis
* `bitSide`  : properties whose behaviour is controlled by the Bit axis
-/
inductive GlobalProperty
  | cutSide
  | bitSide
  deriving Repr, DecidableEq

/--
Dependency profile of a global property with respect to the two axes:

* `dependsOnCut` / `dependsOnBit` say where the property actually lives.
-/
structure PropertyDependency where
  prop         : GlobalProperty
  dependsOnCut : Bool
  dependsOnBit : Bool
  deriving Repr

/--
A property that is structurally tied to the Cut axis (independent of Bit).
-/
def cutDominatedProperty : PropertyDependency :=
  { prop := .cutSide, dependsOnCut := true, dependsOnBit := false }

/--
A property that is structurally tied to the Bit/Ω axis (independent of Cut).
-/
def bitDominatedProperty : PropertyDependency :=
  { prop := .bitSide, dependsOnCut := false, dependsOnBit := true }

/-! ## 5. Hooks for later: connecting Δ and Ω to profiles -/

/--
Placeholder structure for attaching a *concrete* profile to an object.

Later, you can instantiate `α` with:
* traces (`Trace`),
* real numbers / codes,
* theories, etc.

and fill in how its Cut/Bit ranks and Δ-bands are computed.
-/
structure Profiled (α : Type) where
  carrier   : α
  profile   : NumberProfile
  deriving Repr

end Profiles
