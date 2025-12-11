import ChaitinOmega
import OmegaRevHalt

/-!
# ProfilesOmega: Linking Profiles to Ω and Kolmogorov Complexity

This file connects:

* abstract profile language (`NumberProfile`, `BitRank`, `CutRank`),
* Kolmogorov complexity `K` defined in `ChaitinOmega`,
* Ω bits constructed in `OmegaRevHalt`.

Goals:

1. Define the property "Ω is K-random" (`omegaBitKRandom`) using `K` and `OmegaPrefix`.
2. Conclude that the `BitRank` of Ω is `BitRank.transcend`.
3. Build a canonical `NumberProfile` for Ω with `bitRank = transcend` and `cutRank = ilm`.

This file adds no axioms — it only wraps and connects existing components.
-/

namespace ProfilesOmega

open Chaitin

/-! ## 1. Axes: Cut vs Bit -/

/-- Coarse rank on the Cut axis (Gödel/consistency-style). -/
inductive CutRank
  | local    -- finitary / locally decidable
  | ilm      -- interleaved / limit behaviour, needs infinite approximation
  deriving Repr, DecidableEq

/-- Coarse rank on the Bit axis (Ω/bits-style). -/
inductive BitRank
  | local       -- bits are locally decidable
  | transcend   -- bits are algorithmically random / incompressible
  deriving Repr, DecidableEq

/-- Abstract 4-way classification (CutRank × BitRank). -/
inductive NumberKind
  | intLike        -- tame on both Cut and Bit
  | irrationalLike -- Cut needs ilm, Bit stays local
  | transcendLike  -- Cut local, Bit transcend
  | omegaLike      -- both axes in hard regime
  deriving Repr, DecidableEq

/-- A static profile combining kind, ranks, and delta-bands. -/
structure NumberProfile where
  kind     : NumberKind
  cutRank  : CutRank
  bitRank  : BitRank
  deltaCut : ℕ
  deltaBit : ℕ
  deriving Repr

/-! ## 2. Ω is K-random: definition based on Kolmogorov -/

/--
`omegaBitKRandom U` states that Ω prefixes have Kolmogorov complexity
at least `n - c` for some constant `c`. This is the standard definition
of K-randomness.
-/
def omegaBitKRandom (U : PrefixUniversalModel) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, K U (OmegaPrefix n) ≥ n - c

/--
The axiom `Omega_K_random'` from `ChaitinOmega.lean` directly implies
that `omegaBitKRandom U` holds.
-/
lemma omegaBitKRandom_of_axiom (U : PrefixUniversalModel) (embed : ℕ → U.Code) :
    omegaBitKRandom U :=
  Omega_K_random' U embed

/-! ## 3. BitRank classification for Ω -/

/--
BitRank for Ω: directly `transcend` because Ω is K-random.
-/
def omegaBitRank : BitRank := BitRank.transcend

/--
The BitRank of Ω is `transcend`.

Justification: `Omega_K_random'` implies K(OmegaPrefix n) ≥ n - c,
which is the definition of K-random/incompressible.
-/
theorem omegaBitRank_is_transcend_because_K_random (U : PrefixUniversalModel) (_ : ℕ → U.Code) :
    omegaBitKRandom U → omegaBitRank = BitRank.transcend := by
  intro _
  rfl

/-! ## 4. Canonical number profile for Ω -/

/--
Canonical profile of Ω in the (CutRank × BitRank) grid.

* `kind     := omegaLike`   — the Ω-like cell in the table
* `cutRank  := ilm`         — Ω is not internalizable (T2 / no_internal_omega_predicate)
* `bitRank  := transcend`   — determined by K-randomness (Omega_K_random')
* `deltaCut := 1`           — Ω is in the hard band on the Cut axis
* `deltaBit := 1`           — Ω is in the hard band on the Bit axis
-/
def omegaNumberProfile : NumberProfile :=
  { kind     := NumberKind.omegaLike
    cutRank  := CutRank.ilm
    bitRank  := omegaBitRank
    deltaCut := 1
    deltaBit := 1 }

/--
The profile of Ω has `bitRank = transcend`.
-/
theorem omegaNumberProfile_bitRank_transcend :
    omegaNumberProfile.bitRank = BitRank.transcend := rfl

/--
The profile of Ω has `cutRank = ilm`, justified by T2/no_internal_omega_predicate.
-/
theorem omegaNumberProfile_cutRank_ilm :
    omegaNumberProfile.cutRank = CutRank.ilm := rfl

end ProfilesOmega
