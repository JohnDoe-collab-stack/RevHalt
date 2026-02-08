# Asymmetry as a Bridge Between Two Reference Frames

## 1) Two Well-Defined Reference Frames

### R1 — Classical Frame of Symmetry

- **Setting**: an object X with a group of symmetries G (or a symmetric monoidal structure).
- **Symmetry**: invariance under G (or global factor exchange).
- **Classical asymmetry**: deviation from invariance (symmetry breaking, non-commutativity, non-invariance).

### R2 — Frame of Dissociation

- **Setting**: an independence relation (⊥) conditioning a partial parallel (⊗), defined only if f ⊥ g, a sequential (∘), and a local interchange.

- **Measures (I)**:
  - Parallel induces a parallel aggregation (⊕) via I(f ⊗ g) = I(f) ⊕ I(g) (when defined).
  - Series induces a serial aggregation (⊙) via I(g ∘ f) ≽ I(g) ⊙ I(f) (subadditivity).

- **Classification**: only four stable arithmetics appear: (max,+), (min,+), (+,+), (+,max).

  > **Note**: Only (max,+) and (min,+) are semirings in the classical sense (⊙ distributes over ⊕). The pairs (+,+) and (+,max) satisfy the weaker local interchange axiom but not global distributivity. The term "arithmetic" here means (⊕,⊙) satisfying H1–H2, not necessarily a semiring.

- **Geometric neutrality**: only precedences (pomset) matter, not drawing or layout.

---

## 2) Asymmetry as a Bridge Between R1 and R2

### Definition

Asymmetry quantifies how far one moves from R1 to R2 (and conversely).

### Observables

- **Parallelizability** p ∈ [0,1] — proportion of pairs actually parallelizable.

- **Interchange locality** κ_I ∈ [0,1] — fraction of interchange squares where the equality

  ```
  I((f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)) = I((f₁ ∘ f₀) ⊗ (g₁ ∘ g₀))
  ```

  holds, conditional on both parallels being defined.
  
  > **Clarification**: κ_I measures observational interchange via invariant I, not structural isomorphism. It requires a **square** of four morphisms (f₀, f₁, g₀, g₁) with f₀ ⊥ g₀ and f₁ ⊥ g₁.

- **Interchange defect** E_I ≥ 0 — quantitative amplitude of interchange failure.

  For a square (f₀, f₁, g₀, g₁) with both parallels defined, let:

  ```
  p_sq = (f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)      (parallel-first)
  q_sq = (f₁ ∘ f₀) ⊗ (g₁ ∘ g₀)      (series-first)
  ```

  **Pointwise defect** (bounded in [0,1)):

  ```
  E_I(f₀,f₁,g₀,g₁) = |I(p_sq) − I(q_sq)| / (1 + |I(p_sq)| + |I(q_sq)|)
  ```

  > **Why this normalizer**: The denominator 1 + |a| + |b| guarantees E_I ∈ [0,1) unconditionally, regardless of the sign or magnitude of I. Unlike the v1 formula max(1,|a|,|b|), this is robust to signed invariants.

  **Aggregate**: E_I = median or P95 over all tested squares.

  > **Distinction κ_I vs E_I**: κ_I counts how often interchange holds exactly (Boolean rate); E_I measures by how much it fails (continuous amplitude). Both are needed: a system can have κ_I = 0.5 with tiny E_I (many small violations) or κ_I = 0.9 with large E_I (rare but severe violations).

### Compact Index (bounded)

```
A★ = α(1 − p) + β(1 − κ_I) + γ E_I
```

with **α, β, γ > 0** and α + β + γ = 1.

> **Strict positivity required**: The biconditionals below hold only when α, β, γ > 0. If any weight is zero, the corresponding observable is ignored and the equivalences weaken to implications.

- **A★ = 0** ⇔ p = 1, κ_I = 1, E_I = 0 (total independence, exact interchange).
- **A★ = 1** ⇔ p = 0, κ_I = 0, E_I = 1 (no independence, no interchange, maximal defect).

> **What A★ = 0 means**: The system has full parallelism and exact interchange. This is compatible with **any** arithmetic regime — including tropical (max,+) where ⊕ ≠ ⊙ by design. A★ measures structural independence/interchange, not whether ⊕ and ⊙ coincide as operations.

**Non-normalized variant** (fixed weights, for quick computation):

```
A = 0.5 * ((1 − p) + (1 − κ_I)) + E_I
```

> Implicit weights ≈ (0.25, 0.25, 1) after renormalization: disproportionate emphasis on E_I. Bounds: A ∈ [0, 2) since E_I ∈ [0,1). A★ is the canonical form; A is a convenience variant.

### Convention When p = 0

When no pair is independent, no ⊗-context exists, so κ_I and E_I are ratios over an empty set.

**Convention**: set κ_I := 1 and E_I := 0 (no penalty beyond (1−p) = 1).

**Rationale**: the entire asymmetry is already captured by p = 0. Penalizing κ_I or E_I would double-count the absence of parallelism.

Under this convention: A★ = α when p = 0 (only the parallelizability term contributes).

### Axioms for a Proper Measure

1. **Normalization**: A★ = 0 when p = 1, κ_I = 1, E_I = 0; increases when independence or interchange is restricted.
2. **Re-timing invariance**: A★ is unchanged under transformations preserving precedences.
3. **Monotonicity (conditional)**: expanding independence ⇒ p ↑. If additionally the new independent pairs satisfy interchange at a rate ≥ κ_I (and with defect amplitude ≤ E_I), then κ_I is non-decreasing and E_I is non-increasing, so A★ ↓.

  > **Caveat on κ_I**: Since κ_I is a conditional ratio, adding independent pairs that fail interchange can decrease κ_I. For example: 7/8 success rate, add 4 pairs with 1 success → κ_I = 8/12 = 2/3 < 7/8. Monotonicity of κ_I requires the new pairs to satisfy interchange at least at the current rate.

---

## 3) Symmetry – Asymmetry – Dissymmetry (Trio)

- **Symmetry (R1)**: total parallelism, exact interchange (p = 1, κ_I = 1, E_I = 0).

- **Asymmetry (bridge)**: differing roles between parallel (conditional) and serial (always defined), measured by A★.

- **Dissymmetry (profile)**: how the gap manifests, classified by

  ```
  (⊕,⊙) ∈ { (max,+), (min,+), (+,+), (+,max) }
  ```

  with: idempotent ⊕ (tropical) or not, presence/absence of absorption for ⊙, max/min orientation, and residuation (numeric vs implication in +,max).

  > **Note**: The dissymmetry profile (choice of arithmetic) is **orthogonal** to the asymmetry index A★. A system can have A★ = 0 in any of the four regimes. The profile classifies *how* invariants aggregate; A★ classifies *how constrained* the independence structure is.

---

## 4) Structural Statements (Informal but Testable)

- **L1 — Symmetric limit**: A★ = 0 ⇒ full independence and exact interchange hold; parallel behaves as total.

- **L2 — Host factorization**: A★ > 0 ⇒ every stable invariant factorizes into one of the four hosts (max+, min+, ++, +max).

- **L3 — Non-exchange cost**: if residuation exists,

  ```
  δ_I(f₀,f₁,g₀,g₁) = I(p_sq) ▷ I(q_sq)   (right residual of interchange square)
  ```

  Then:
  - **(⇐)** A★ = 0 (with α, β, γ > 0) ⇒ δ_I ≡ 0.
  - **(⇒, qualified)** δ_I ≡ 0 ⇒ E_I = 0 and κ_I = 1, but does **not** imply p = 1. Full equivalence: δ_I ≡ 0 **and** p = 1 ⇔ A★ = 0.

  > **Why the unqualified ⇒ fails**: If p = 0, no interchange square exists, so δ_I is vacuously ≡ 0, yet A★ = α > 0.

- **L4 — Geometric neutrality**: A★, p, κ_I, E_I invariant under all precedence-preserving transformations.

---

## 5) Quick Numerical Example

### Setup

Four tasks with durations: f₀ = 2, f₁ = 3, g₀ = 1, g₁ = 4. Independence: f₀ ⊥ g₀ and f₁ ⊥ g₁.

Invariant: L (makespan) in (max,+).

### Computing p

Six task pairs total: (f₀,f₁), (f₀,g₀), (f₀,g₁), (f₁,g₀), (f₁,g₁), (g₀,g₁).
Independent pairs: (f₀,g₀) and (f₁,g₁) → p = 2/6 = 1/3.

### Computing the interchange square

```
p_sq = (f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)
     = max(f₁,g₁) + max(f₀,g₀)     [in (max,+)]
     = max(3,4) + max(2,1)
     = 4 + 2 = 6

q_sq = (f₁ ∘ f₀) ⊗ (g₁ ∘ g₀)
     = max(f₁+f₀, g₁+g₀)           [in (max,+)]
     = max(3+2, 4+1)
     = max(5, 5) = 5
```

### Computing κ_I and E_I

I(p_sq) = 6, I(q_sq) = 5 → interchange fails (6 ≠ 5).

- κ_I = 0/1 = **0** (this square fails).
- E_I = |6 − 5| / (1 + 6 + 5) = 1/12 ≈ **0.083**.

### Computing A★

With α = β = γ = 1/3:

```
A★ = (1/3)(1 − 1/3) + (1/3)(1 − 0) + (1/3)(0.083)
   = (1/3)(2/3) + (1/3)(1) + (1/3)(0.083)
   = 0.222 + 0.333 + 0.028
   = 0.583
```

→ High A★ zone: tropical regime appropriate.

### Interchange failure in (max,+): why it's generic

The interchange identity in (max,+) reads:

```
max(f₁,g₁) + max(f₀,g₀) = max(f₁+f₀, g₁+g₀)
```

This holds only when the same "lane" dominates in both layers (e.g., f₁ ≥ g₁ **and** f₀ ≥ g₀). When dominance switches lanes (f₁ < g₁ but f₀ > g₀), the LHS picks the max per layer independently while the RHS picks the max of sums — these generically differ by the "cross" terms.

### Geometry neutrality

Redrawing the same precedence graph (same pomset) differently → same (p, κ_I, E_I, A★). ✓

---

## 6) Dictionary Definitions

- **Asymmetry (classical)**: lack of invariance under a set symmetry (group, global exchange).

- **Asymmetry (dissociative)**: quantified restriction of independence and interchange, measured by A★ = α(1−p) + β(1−κ_I) + γE_I; the dissymmetry details its arithmetic profile (max+, min+, ++, +max).

---

## 7) Bounds and Normalization

- **Minimal gap**: A★ = 0 when p = 1, κ_I = 1, E_I = 0 (requires α, β, γ > 0 for converse).
- **Maximal gap**: A★ → 1 when p = 0, κ_I = 0, E_I → 1 (E_I ∈ [0,1) so A★ < 1 strictly; A★ = 1 is a supremum, not attained).

  > **Technical note**: Since E_I = |a−b|/(1+|a|+|b|) < 1 strictly, A★ = 1 is never exactly attained. If exact attainment is desired, use E_I = |a−b|/max(1,|a|+|b|) instead (which reaches 1 when one of a,b is 0 and the other is ≥ 1). The choice is a modeling decision; the [0,1)-valued version is analytically more convenient.

- **Weights** (α, β, γ > 0) tune the relative importance of independence, interchange rate, and interchange amplitude.

---

## 8) Effect of A★ on the Four Arithmetics

### 8.1 Regime Selection by A★

- **A★ ≈ 0**: full independence and interchange → any regime works; choose by invariant semantics.
- **A★ rising**: parallelism becomes conditional, interchange local → regime selection matters more; tropical regimes (max,+, min,+) and (+,max) become the natural choices for depth/distance/width measures.

  > **Clarification vs v1**: A★ does not select the arithmetic (that depends on the invariant). A★ indicates how much the independence/interchange structure constrains computation. At high A★, the difference between regimes becomes operationally decisive.

### 8.2 Linking Regimes

- **Duality**: (max,+) ↔ (min,+) by order reversal.
  
  > **Note**: (+,+) is self-dual; (+,max) has different structure (no simple duality).

- **Additive approximation of max** (LogSumExp):

  ```
  max(x₁,…,xₙ) ≤ (1/β) · log(Σ eᵝˣⁱ) ≤ max(xᵢ) + (log n)/β
  ```
  
  > **Note**: The max is a **lower bound**, not upper. Large β when interchange is nearly exact (low E_I: controlled error); otherwise use exact tropical operators.

- **Residuation**: numeric in (max,+), (min,+), (+,+); logical (implicative) in (+,max).
  The larger A★, the more decisive this distinction.

### 8.3 Relations Valid for Any A★

- For nonnegative values: additive cost C₊₊ always bounds depth L_{max+} and distance d_{min+} (since the total sum ≥ any single path).

  > **Note on width W_{+max}**: W = max over antichains S of Σ_{s∈S} I(s). Every antichain is a subset of all tasks, so W ≤ C₊₊. This bound holds because parallel-branch sums are partial sums of the total.

- Geometric neutrality: depends on the pomset, not on drawing.
- Rigid classification: once the independence structure is non-trivial (p < 1 or interchange imperfect), the four regimes give genuinely different results.

### 8.4 Phase Diagram (indicative thresholds)

```
A★: 0 ───── 0.15 ───────── 0.5 ───────────────────────── 1.0
     any regime ok   regime choice matters    regime choice critical
```

> **Note**: Thresholds are heuristic; calibrate for specific domains. At low A★, all four regimes give similar results because interchange holds nearly everywhere.

---

## 9) Practical Checklist

1. Fix the invariant I and the arithmetic regime (⊕,⊙).
2. Enumerate interchange squares (quadruples f₀,f₁,g₀,g₁ with f₀⊥g₀, f₁⊥g₁).
3. Measure p (parallelizability), κ_I (interchange success rate), E_I (interchange defect amplitude).
4. Choose weights (α, β, γ > 0) and compute A★.
5. Assess regime sensitivity: at low A★, results are robust to regime choice; at high A★, verify regime appropriateness.
6. Apply the corresponding operators (closures, min/max-plus convolutions, residuation).
7. Check global bounds using additive cost when relevant.

---

## 10) TL;DR

- **Asymmetry** measures the gap between classical and dissociative frames via (p, κ_I, E_I) → index A★.
- **A★ = 0**: full independence + exact interchange. **A★ > 0**: restricted independence or imperfect interchange.
- **A★** is geometry-invariant and indicates how sensitive computations are to the choice among (max,+), (min,+), (+,+), (+,max).

---

## 11) Q-Symmetry (QSym) — Quantified Bridge

### Definition

- **Triplet**: QSym = (p, κ_I, E_I) with p ∈ [0,1], κ_I ∈ [0,1], E_I ∈ [0,1).
- **Index**: A★ = α(1−p) + β(1−κ_I) + γE_I, with α, β, γ > 0 and α+β+γ=1.
  - A★ = 0 ⇔ p = 1, κ_I = 1, E_I = 0
  - A★ > 0 ⇔ at least one of: p < 1, κ_I < 1, E_I > 0
- **Non-normalized**: A = 0.5((1−p)+(1−κ_I)) + E_I (fixed-weight variant; see §2)
- **Convention**: if p = 0 → set κ_I := 1, E_I := 0 (avoid double-counting).

### Properties

1. **Normalization**: A★ = 0 when p = 1, κ_I = 1, E_I = 0; grows when independence or interchange degrades.
2. **Invariance**: stable under re-timing (geometry-neutral).
3. **Monotonicity (conditional)**: expanding independence ⇒ p ↑; κ_I non-decreasing and E_I non-increasing provided new pairs satisfy interchange at rate ≥ κ_I with defect ≤ E_I.

### Arithmetic Sensitivity Rule

| Zone | A★ Range | Interpretation |
|------|----------|----------------|
| Low | A★ ≲ 0.15 | All regimes give similar results; interchange nearly exact |
| Intermediate | 0.15 ≲ A★ ≲ 0.5 | Regime choice matters for some invariants |
| High | A★ ≳ 0.5 | Regime choice critical; results diverge significantly |

> Thresholds indicative; calibrate for context.

### Non-Exchange Cost (Corrected)

If residuation exists: δ_I(f₀,f₁,g₀,g₁) = I(p_sq) ▷ I(q_sq).

- δ_I ≡ 0 ⇒ E_I = 0 and κ_I = 1 (but not necessarily p = 1).
- Full equivalence: δ_I ≡ 0 **and** p = 1 ⇔ A★ = 0.

### Practical Algorithm

```
Input: causal graph, independence relation ⊥, invariant I, arithmetic (⊕,⊙)

1) p := (# independent pairs) / (# total pairs)
2) If p = 0: set κ_I := 1, E_I := 0, go to step 5.
3) Enumerate interchange squares S = {(f₀,f₁,g₀,g₁) : f₀⊥g₀, f₁⊥g₁}
   For each square, compute:
     p_sq := I((f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀))
     q_sq := I((f₁ ∘ f₀) ⊗ (g₁ ∘ g₀))
     success := (p_sq = q_sq)
     defect := |p_sq − q_sq| / (1 + |p_sq| + |q_sq|)
4) κ_I := (# successes) / |S|
   E_I := median(defect) or P95(defect)
5) A★ := α(1−p) + β(1−κ_I) + γE_I     (α, β, γ > 0, sum = 1)
6) Assess regime sensitivity based on A★ zone; apply operators accordingly.
```

---

## 12) Decision Policies for A★ — Discrete vs Continuous

### Discrete Threshold Policy

- **Parameters**: two thresholds θ₁ < θ₂.
- **Decision**:
  - Low sensitivity (any regime) if A★ < θ₁
  - Mixed (verify regime choice for key invariants) if θ₁ ≤ A★ < θ₂
  - High sensitivity (regime-specific operators required) if A★ ≥ θ₂
- Thresholds can be set by quantiles, risk minimization, or domain rules.

### Continuous Mixture Policy

**Two-regime version** (additive vs tropical aggregate):

```
w_add(A★) = exp(−λA★)
w_trop(A★) = 1 − w_add(A★)
```

Output: F(A★) = w_add · F_{++} + w_trop · F_trop, where F_trop is the tropical operator selected by invariant type.

**Four-regime version** (full softmax):

```
w_r(A★) = exp(s_r(A★)) / Σ_{r'} exp(s_{r'}(A★))
```

where s_r are regime-specific score functions (e.g., linear in A★ with domain-set slopes), and r ∈ {max+, min+, ++, +max}.

Output: F(A★) = Σ_r w_r(A★) · F_r.

> **Note**: The two-regime version is a simplification; use the four-regime softmax when all four arithmetics are simultaneously relevant.

**Advantage**: smooth transitions, no oscillation around thresholds.

### Hysteresis

Two thresholds per transition: θ_on < θ_off to avoid back-and-forth in gray zones.

---

## Incompleteness Results

### Assumptions

- **H1**: partial parallel (⊗), sequential (∘), local interchange.
- **H2**: invariant I with I(f⊗g)=I(f)⊕I(g) (when defined) and I(g∘f) ≽ I(g)⊙I(f).
- **H3**: two canonical families:
  - *Tropical*: idempotent ⊕ (max/min), zero of ⊕ absorbing for ⊙=+.
  - *Quantitative*: ⊕ = + (non-idempotent), no absorption for ⊙ ∈ {+, max}.
- **H4**: factorization of I reflects equality (no confusion between x and 2x).
- **Convention**: distinguish 𝟘 (zero of ⊕) from 0 = I(id) (unit of ⊙ when ⊙ = +).

### Result 1 — Structural Incompleteness (no-go)

**Statement**: No scalar arithmetic (S, ⊕, ⊙, 𝟘, 𝟙) common to all invariants can be simultaneously isomorphic to a tropical host (max,+ or min,+) and an additive one (+,+ or +,max).

**Reason**: tropical ⊕ is idempotent and 𝟘 is absorbing for ⊙=+, both properties absent in additive regimes.

### Result 2 — Observational Incompleteness

**Statement**: Under geometric neutrality, two non-isomorphic pomsets can share identical invariant values.

**Example** (all durations = 1):

```
G1: (A || B) then C    →  L=2, W=2, C=3
G2: A then (B || C)    →  L=2, W=2, C=3
```

> **Note**: The rank R (counting barriers) can distinguish such cases when additional synchronization structure is present.

### Conjecture 1 — Proof/Decision Incompleteness (Open Problem)

**Conjecture**: The inequality logic generated by ⊗, ∘, and local interchange, valid for all independence relations, admits no finite, complete axiomatisation.

**Precise formulation needed**: Define the logic as:

- Signature: (⊗, ∘, ≤) with ⊗ partial
- Axiom schemes: interchange locality, unit laws, associativity
- Target: completeness relative to PCM-based semantics

**Reason**: interchange locality depends on the fine structure of independence; families (e.g., diamond lattices) require unbounded rule schemes.

### Role of A★ (Bridge)

- **A★ = 0**: full independence and exact interchange → all regimes agree on interchange squares; structural no-go becomes moot (one can work in any regime).
- **A★ > 0**: the four-host classification becomes necessary (Result 1), observation via (L,W,C,…) becomes insufficient (Result 2), and a finite global axiom base is unlikely (Conjecture 1).

---

## Summary of Corrections

### v2 → v3 (conceptual)

| # | Section | Correction |
|---|---------|------------|
| 1 | §2, E → E_I | Replaced "aggregation gap" (series vs parallel) by "interchange defect" (parallel-first vs series-first in a square). E_I measures interchange failure, not ⊕/⊙ difference. |
| 2 | §2, A★=0 | Removed "⊕ ≈ ⊙". A★ = 0 now means (p=1, κ_I=1, E_I=0), compatible with any arithmetic regime. |
| 3 | §5 | Replaced 2-task example (cannot form interchange square) with 4-morphism example. Showed explicit interchange failure in (max,+). |
| 4 | §2, convention | Added p=0 convention: κ_I := 1, E_I := 0 to avoid double-counting. |
| 5 | §3, §8 | Decoupled arithmetic profile (dissymmetry) from A★: the regime is chosen by invariant semantics; A★ indicates how much the choice matters. |
| 6 | §7 | Noted A★ = 1 is a supremum (not attained) since E_I ∈ [0,1). |
| 7 | §8.4 | Phase diagram now describes "sensitivity of regime choice", not "which regime to use". |

### v1 → v2 (technical, retained)

| # | Section | Correction |
|---|---------|------------|
| 8 | §2 | α,β,γ > 0 strictly (for biconditionals) |
| 9 | §2, Axiom 3 | Monotonicity of κ conditional on new-pair interchange rate |
| 10 | §4, L3 | Fixed false biconditional: δ_I ≡ 0 ⇏ A★ = 0 when p < 1 |
| 11 | §8.3 | Added justification for C₊₊ ≥ W_{+max} |
| 12 | §12 | Separated two-regime and four-regime mixture policies |
| 13 | §Incompleteness | Renamed "Result 3" → "Conjecture 1" |
| 14 | §1 | Note: (+,+) and (+,max) are not semirings |

---

## To-Do

- [ ] Write full proof of Result 1 (idempotence/absorption).
- [ ] Record explicit counterexample for Result 2 (with R distinguishing).
- [ ] For Conjecture 1: define the logic precisely, build a parametric family, and show non-finiteness (or relative completeness for restricted classes like series-parallel).
- [ ] Determine precise conditions under which monotonicity of κ_I holds.
- [ ] Investigate whether E_I aggregation (median vs P95 vs mean) affects the phase diagram thresholds.
- [ ] Provide a worked example in (+,+) showing A★ = 0 with interchange exact (confirming regime-independence of the index).

---
