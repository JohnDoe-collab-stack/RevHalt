# On_the_side: Experimental Modules

This folder contains **experimental modules** that extend the RevHalt framework
with profile-based classification and quantitative invariants.

## Files

| File | Purpose |
|------|---------|
| `RevHaltDelta.lean` | Finite halting counters (countTrue, allTrue, deltaScaled) and DR0/DR1 theorems |
| `Profiles.lean` | Cut×Bit classification grid (CutRank, BitRank, NumberKind, NumberProfile) |
| `ProfilesOmega.lean` | Links profiles to Ω via Kolmogorov complexity K |

---

## Architecture: Separation of Concerns

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      SEPARATION OF CONCERNS                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐         │
│  │   Cut Axis      │    │   Bit Axis      │    │   Complexity    │         │
│  │  (T1/T2/T3)     │    │  (K/Ω)          │    │  (theoryLength) │         │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘         │
│           │                      │                      │                   │
│           ▼                      ▼                      ▼                   │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐         │
│  │  CutRank        │    │  BitRank        │    │  codeLength     │         │
│  │  {local, ilm}   │    │  {local,transcend}   │  (ℕ)            │         │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘         │
│           │                      │                      │                   │
│           └──────────┬───────────┴──────────────────────┘                   │
│                      ▼                                                      │
│              ┌─────────────────┐                                            │
│              │  NumberProfile  │                                            │
│              │  (kind, ranks,  │                                            │
│              │   delta-bands)  │                                            │
│              └─────────────────┘                                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Key Insight: The Wrapper Simplified

With `ProfilesOmega`, the wrapper from `ChaitinOmega` can be understood purely in terms of profiles:

```
                    WRAPPER
                       ↓
┌──────────────────────────────────────────────────────────┐
│  Input:  Theory T with "bit-local" profile on [0,n) of Ω │
│          (DecidesBit for all k < n)                      │
│                                                          │
│  Output: Program of length ≤ theoryLength(T) + C         │
│          producing an "omegaLike" object (OmegaPrefix n) │
└──────────────────────────────────────────────────────────┘
```

The wrapper is a **pure bridge** between:
- **Bit-locality** (profile of T on the Bit axis)
- **Description-length** (complexity profile via K)

---

## ProfilesOmega: Grounding in K

`ProfilesOmega.lean` anchors the classification in Kolmogorov complexity:

```lean
-- 1. Formal definition of K-randomness
def omegaBitKRandom (U : PrefixUniversalModel) : Prop :=
  ∃ c, ∀ n, K U (OmegaPrefix n) ≥ n - c

-- 2. Derived from existing axiom
lemma omegaBitKRandom_of_axiom : omegaBitKRandom U :=
  Omega_K_random' U embed

-- 3. BitRank follows from K-randomness
theorem omegaBitRank_is_transcend_because_K_random :
    omegaBitKRandom U → omegaBitRank = BitRank.transcend
```

**Before**: "Ω is transcend because we say so"  
**After**: "Ω is transcend **because K(prefixes) ≥ n - c**"

---

## The 2×2 Classification Grid

| NumberKind | CutRank | BitRank | Example |
|------------|---------|---------|---------|
| intLike | local | local | 42, ℤ |
| irrationalLike | ilm | local | √2 |
| transcendLike | local | transcend | (computable transcendental) |
| **omegaLike** | **ilm** | **transcend** | **Ω** |

Ω is the **canonical prototype** for `omegaLike`:
- `bitRank = transcend` justified by K (Omega_K_random')
- `cutRank = ilm` justified by T2 (no_internal_omega_predicate)

---

## Modular Responsibilities

| Component | Responsibility | File |
|-----------|----------------|------|
| T1/T2/T3 | Cut axis (internal decidability) | `RevHalt.lean` |
| K, OmegaPrefix | Bit axis (complexity) | `ChaitinOmega.lean` |
| Wrapper | Bridge bit-local → short program | `ConcreteUniversal.lean` |
| Profiles | Cut×Bit vocabulary | `Profiles.lean` |
| ProfilesOmega | Anchor K → BitRank | `ProfilesOmega.lean` |

---

## Building

These files are not in the main Lake build path. To compile:

```bash
lake env lean On_the_side/RevHaltDelta.lean
lake env lean On_the_side/Profiles.lean
lake env lean On_the_side/ProfilesOmega.lean
```

All files compile without errors or `sorry`.
