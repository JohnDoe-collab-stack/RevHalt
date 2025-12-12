# RevHalt Framework: Three-Axis Theory of Computation

## Overview

This document synthesizes the **RevHalt framework**, a unified formal approach to
computational limits structured around three orthogonal axes:

| Axis | Focus | Module |
|------|-------|--------|
| **Cut** | Internal decidability | RevHalt (T1/T2/T3) |
| **Bit** | Compressibility | ChaitinOmega (K, Ω) |
| **Time** | Resources | Complexity (P_rev, NP_rev) |

---

## 1. The Cut Axis: T1/T2/T3

### Core Idea

The **Cut axis** concerns whether halting can be internalized by a theory.

### Theorems

**T1 (Canonicity):** There is essentially one notion of halting.
```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T
```
Any correct detection/reversal pair yields the same halting predicate.

**T2 (Impossibility):** No internal total predicate can decide halting.
```lean
theorem T2_impossibility (ctx : TuringGodelContext' Code PropT) :
    ¬∃ H_internal, TotalCorrectComplete ctx H_internal
```
Diagonal argument: self-reference breaks any claimed total halting oracle.

**T3 (Complementarity):** Partial theories can be extended, but never completed.
```lean
theorem T3_strong :
    ∀ (n : ℕ), ∃ (family : Fin n → (Code → Prop)),
      (∀ i j, i ≠ j → Independent (family i) (family j)) ∧ ...
```
Infinite families of complementary partial halting oracles exist.

### CutRank Classification

| CutRank | Meaning | Example |
|---------|---------|---------|
| `local` | Finitely decidable | Computable sets |
| `ilm` | Requires infinite approximation | Halting problem, Ω |

---

## 2. The Bit Axis: Kolmogorov Complexity and Ω

### Core Idea

The **Bit axis** concerns whether information can be compressed.

### Key Definitions

```lean
axiom K (U : PrefixUniversalModel) : Output → ℕ  -- Kolmogorov complexity

axiom Omega_K_random' (U : PrefixUniversalModel) :
    ∃ c, ∀ n, K U (OmegaPrefix n) ≥ n - c  -- Ω is K-random
```

### Chaitin's Bound

```lean
theorem Chaitin_bound (U : PrefixUniversalModel) (embed : ℕ → U.Code)
    (T : RecursiveTheory U) :
    ∃ C, ∀ n, TheoryDecidesBitRange U embed T n → n ≤ theoryLength U T + C
```

**Interpretation:** A theory of description length L can decide at most L + C bits of Ω.

### BitRank Classification

| BitRank | Meaning | Example |
|---------|---------|---------|
| `local` | Compressible | Rationals, algebraics |
| `transcend` | Incompressible (K-random) | Ω |

---

## 3. The Time Axis: Complexity Classes

### Core Idea

The **Time axis** concerns computational resources (time bounds).

### RevHalt-native Definitions

```lean
def HaltsInTime (T : Trace) (t : ℕ) : Prop := ∃ n ≤ t, T n

def inP {α : Type} (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ (T : α → Trace) (f : ℕ → ℕ),
    PolyBound f ∧ DecidableInTime T L size f

def inNP {α : Type} (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ β R V g, PolyBound g ∧ ... ∧ (∀ x, L x ↔ ∃ y, R x y)
```

**Important:** These are **one-sided** classes (halt on YES only).

### TimeRank Classification

| TimeRank | Meaning |
|----------|---------|
| `poly` | Polynomial time |
| `superPoly` | Super-polynomial or unknown |

---

## 4. The Canonical Hard Object: Ω and LOmega

### Ω's Profile

Chaitin's Omega occupies the **maximal difficulty** position:

```
CutRank  = ilm         ← T2 applies (no_internal_omega_predicate)
BitRank  = transcend   ← Omega_K_random'
TimeRank = superPoly   ← Chaitin_complexity_barrier
```

### LOmega: The Language of Ω Bits

```lean
def LOmega : ℕ × Bool → Prop
  | (k, true)  => OmegaBit U.toComputabilityModel embed k
  | (k, false) => ¬ OmegaBit U.toComputabilityModel embed k

def profiledLOmega : ProfiledLanguage (ℕ × Bool) :=
  { L := LOmega U embed, size := sizeOmega, profile := omegaDerivedProfile }
```

### Key Barrier Theorem

```lean
theorem LOmega_prefix_undecidable (T : RecursiveTheory U) :
    ∃ C, ∀ k, k > theoryLength U T + C → ¬ TheoryDecidesBitRange U embed T k
```

---

## 5. Connection: T3 "Reversed" on Time

### Classical T3 (Cut axis)

> "No single theory captures all halting truths; but any partial theory can be extended."

### Conjecture: Time-axis analog

> "No single polynomial procedure captures all languages of profile omegaDerivedProfile;
> but any finite family of procedures leaves gaps that can be witnessed."

### Formalization Pathway

1. **P_NP_separation_conjecture:** P_rev ≠ NP_rev
2. **transcend_barrier_conjecture:** bitRank.transcend → ∉ P_rev
3. **ilm_barrier_conjecture:** cutRank.ilm → resists uniform poly

---

## 6. The Research Program

### Proven (Formal)

| Result | Status |
|--------|--------|
| T1/T2/T3 | ✅ Proven |
| Chaitin_bound | ✅ Proven (from axioms) |
| P ⊆ NP | ✅ Proven |
| LOmega_prefix_undecidable | ✅ Proven |

### Conjectured (Open)

| Conjecture | Status |
|------------|--------|
| P_rev ≠ NP_rev | Open |
| transcend → ∉ P_rev | Open (linked to K) |
| ilm → resists poly | Open (linked to T3) |

### Methodology

```
  Proven Theorems          Profile Classification         Conjectures
  ───────────────          ────────────────────          ────────────
  T2 impossibility    ──►  cutRank = ilm          ──►    ilm_barrier
  Omega_K_random'     ──►  bitRank = transcend    ──►    transcend_barrier
  Chaitin_bound       ──►  timeRank = superPoly   ──►    P_rev ≠ NP_rev
```

---

## 7. Philosophical Summary

The RevHalt framework embodies a single thesis:

> **Everything passes through Halting.**

- **Cut:** Halting cannot be internalized (T2)
- **Bit:** Halting bits are incompressible (Ω K-random)
- **Time:** Halting-based languages resist polynomial bounds (barriers)

Ω is the **universal witness**: it lives at the corner (ilm, transcend, superPoly)
where all three forms of difficulty converge.
