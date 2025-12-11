import Profiles
import ChaitinOmega
import OmegaRevHalt

/-!
# ProfilesOmega: Linking Profiles to Ω and Kolmogorov Complexity

This file connects:

* abstract profile language from `Profiles` (NumberProfile, BitRank, CutRank),
* Kolmogorov complexity `K` defined in `ChaitinOmega`,
* Ω bits constructed in `OmegaRevHalt`.

## Architecture

```
Profiles.lean          (Level 4: pure abstract vocabulary)
      ↑
ProfilesOmega.lean     (Level 5: connects profiles to K/Ω)
      ↑
ChaitinOmega.lean      (Level 2: K, OmegaPrefix, Chaitin bound)
OmegaRevHalt.lean      (Level 1: Ω as cut of H*)
```

This file adds no axioms — it only wraps and connects existing components.
-/

namespace ProfilesOmega

open Chaitin
open Profiles

/-! ## 1. Ω is K-random: definition based on Kolmogorov -/

/--
`omegaBitKRandom U` states that Ω prefixes have Kolmogorov complexity
at least `n - c` for some constant `c`. This is the standard definition
of K-randomness.

Note: The dependency on `embed` is implicit in `OmegaPrefix` (captured
by ChaitinOmega's section variable). We don't expose it here.
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

/-! ## 2. BitRank classification for Ω -/

/--
BitRank for Ω: directly `transcend` because Ω is K-random.
-/
def omegaBitRank : BitRank := BitRank.transcend

/--
The BitRank of Ω is `transcend`.

Justification: `omegaBitKRandom` (from `Omega_K_random'`) is exactly the
K-randomness condition, which we define to correspond to `BitRank.transcend`.
-/
theorem omegaBitRank_is_transcend_because_K_random (U : PrefixUniversalModel) :
    omegaBitKRandom U → omegaBitRank = BitRank.transcend := fun _ => rfl

/-! ## 3. Canonical number profile for Ω -/

/--
Canonical profile of Ω in the (CutRank × BitRank) grid.

* `kind     := omegaLike`   — Ω-like cell
* `cutRank  := ilm`         — Ω is not internalizable (T2 / no_internal_omega_predicate)
* `bitRank  := transcend`   — determined by K-randomness (omegaBitKRandom)
* `deltaCut := 1`           — hard band on Cut axis
* `deltaBit := 1`           — hard band on Bit axis
-/
def omegaNumberProfile : NumberProfile :=
  { kind     := NumberKind.omegaLike
    cutRank  := CutRank.ilm
    bitRank  := omegaBitRank
    deltaCut := 1
    deltaBit := 1 }

/-- The profile of Ω has `bitRank = transcend`. -/
theorem omegaNumberProfile_bitRank_transcend :
    omegaNumberProfile.bitRank = BitRank.transcend := rfl

/-- The profile of Ω has `cutRank = ilm`. -/
theorem omegaNumberProfile_cutRank_ilm :
    omegaNumberProfile.cutRank = CutRank.ilm := rfl

/-- Ω wrapped as a Profiled object. -/
def profiledOmega : Profiled Unit :=
  { carrier := ()
    profile := omegaNumberProfile }

end ProfilesOmega
