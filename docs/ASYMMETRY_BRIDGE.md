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

- **Geometric neutrality**: only precedences (pomset) matter, not drawing or layout.

---

## 2) Asymmetry as a Bridge Between R1 and R2

### Definition

Asymmetry quantifies how far one moves from R1 to R2 (and conversely).

### Observables

- **Parallelizability** p ∈ [0,1] — proportion of pairs actually parallelizable.

- **Exchange locality** κ ∈ [0,1] — fraction of contexts where the interchange equality

  ```
  I((f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)) = I((f₁ ∘ f₀) ⊗ (g₁ ∘ g₀))
  ```

  holds, conditional on both parallels being defined.
  
  > **Clarification**: κ measures observational interchange via invariant I, not structural isomorphism.

- **Aggregation gap** E ≥ 0 — normalized difference between series (⊙) and parallel (⊕) for the chosen invariant.

  **Corrected formula** (ensures E ∈ [0,1]):

  ```
  E = |I(g ∘ f) − I(f ⊗ g)| / max(1, |I(g ∘ f)|, |I(f ⊗ g)|)
  ```

  For vector values, use a norm (ℓ₁ by default).

### Compact Index (bounded)

```
A★ = α(1 − p) + β(1 − κ) + γ E
```

with α, β, γ ≥ 0 and α + β + γ = 1.

- **A★ = 0** ⇔ R1 (total parallelism, global exchange, ⊕ ≈ ⊙).
- **A★ = 1** ⇔ Extreme R2 (no parallelism, no exchange, maximal aggregation gap).

**Non-normalized variant** (if E ∉ [0,1]):

```
A = 0.5 * ((1 − p) + (1 − κ)) + E
```

(bounds [0,2] if E ∈ [0,1]).

### Axioms for a Proper Measure

1. **Normalization**: A★ = 0 in R1; increases when independence is restricted.
2. **Re-timing invariance**: A★ is unchanged under transformations preserving precedences.
3. **Monotonicity**: expanding independence ⇒ p ↑, κ ↑, E ↓ ⇒ A★ ↓.

---

## 3) Symmetry – Asymmetry – Dissymmetry (Trio)

- **Symmetry (R1)**: total parallelism, global exchange, ⊕ and ⊙ operationally indistinguishable.

- **Asymmetry (bridge)**: differing roles between parallel (conditional) and serial (always defined), measured by A★.

- **Dissymmetry (profile)**: how the gap manifests, classified by

  ```
  (⊕,⊙) ∈ { (max,+), (min,+), (+,+), (+,max) }
  ```

  with: idempotent ⊕ (tropical) or not, presence/absence of absorption for ⊙, max/min orientation, and residuation (numeric vs implication in +,max).

---

## 4) Structural Statements (Informal but Testable)

- **L1 — Symmetric limit**: A★ = 0 ⇒ ⊕ ≈ ⊙, parallel behaves as total.

- **L2 — Host factorization**: A★ > 0 ⇒ every stable invariant factorizes into one of the four hosts (max+, min+, ++, +max).

- **L3 — Non-exchange cost**: if residuation exists,

  ```
  δ_I(f,g) = I(g ∘ f) ▷ I(f ⊗ g)   (right residual)
  ```

  Then δ_I ≡ 0 ⇔ A★ = 0 for invariant I.

- **L4 — Geometric neutrality**: A★, p, κ, E invariant under all precedence-preserving transformations.

---

## 5) Quick Numerical Example

Two tasks a, b with durations 2, 3.

- **No conflict**: p = 1. In (max,+):

  ```
  I(a ⊗ b) = max(2,3) = 3
  I(b ∘ a) = 2 + 3 = 5
  E ≈ (5 − 3) / max(1,5,3) = 2/5 = 0.4
  κ ≈ 1 ⇒ small A★
  ```

- **With conflict**: p = 0, a ⊗ b undefined, κ drops, E rises ⇒ large A★.

Same graph redrawn differently → unchanged (geometry-neutral).

---

## 6) Dictionary Definitions

- **Asymmetry (classical)**: lack of invariance under a set symmetry (group, global exchange).

- **Asymmetry (dissociative)**: difference in role between parallel (conditional) and series (always defined), measured by A★; the dissymmetry details its profile (max+, min+, ++, +max).

---

## 7) Bounds and Normalization

- **Minimal gap**: A★ = 0 when p = 1, κ = 1, E = 0.
- **Maximal gap**: A★ = 1 when p = 0, κ = 0, E = 1.
- **Weights** (α, β, γ) tune the relative importance of independence, exchange, and aggregation gap.

---

## 8) Effect of A★ on the Four Arithmetics

### 8.1 Regime Selection by A★

- **A★ ≈ 0**: additive aggregation dominates → (+,+) regime; small series/parallel gap.
- **A★ rising**: parallelism becomes conditional, exchange local → tropical regimes (max,+, min,+) and (+,max) for peak/width measures.

### 8.2 Linking Regimes

- **Duality**: (max,+) ↔ (min,+) by order reversal.
  
  > **Note**: (+,+) is self-dual; (+,max) has different structure (no simple duality).

- **Additive approximation of max** (LogSumExp):

  ```
  max(x₁,…,xₙ) ≤ (1/β) · log(Σ eᵝˣⁱ) ≤ max(xᵢ) + (log n)/β
  ```
  
  > **Corrected**: The max is a **lower bound**, not upper. Large β when A★ small (controlled error); otherwise switch to tropical.

- **Residuation**: numeric in (max,+), (min,+), (+,+); logical (implicative) in (+,max).
  The larger A★, the more decisive this distinction.

### 8.3 Relations Valid for Any A★

- For nonnegative values: additive cost C₊₊ always bounds depth L_{max+}, distance d_{min+}, and width W_{+max}.
- Geometric neutrality: depends on the pomset, not on drawing.
- Rigid classification: once A★ > 0, only the four regimes remain admissible.

### 8.4 Phase Diagram (indicative thresholds)

```
A★: 0 ───── 0.15 ───────── 0.5 ───────────────────────── 1.0
     (+,+)     mixed additive↔tropical       tropical & (+,max)
```

> **Note**: Thresholds are heuristic; calibrate for specific domains.

---

## 9) Practical Checklist

1. Fix the invariant I and define normalized E.
2. Measure p (parallelizability) and κ (exchange locality).
3. Choose weights (α, β, γ) and compute A★.
4. Select the regime (⊕,⊙) according to the A★ zone (low/mid/high).
5. Apply the corresponding operators (closures, min/max-plus convolutions, residuation).
6. Check global bounds using additive cost when relevant.

---

## 10) TL;DR

- **Asymmetry** measures the gap between classical and dissociative frames via (p, κ, E) → index A★.
- **A★ = 0**: symmetric view (R1). **A★ > 0**: dissociative view (R2), classified into four arithmetics.
- **A★** is geometry-invariant and guides the choice among (max,+), (min,+), (+,+), (+,max).

---

## 11) Q-Symmetry (QSym) — Quantified Bridge

### Definition

- **Triplet**: QSym = (p, κ, E) with p, κ, E ∈ [0,1].
- **Index**: A★ = α(1−p) + β(1−κ) + γE, with α+β+γ=1.
  - A★ = 0 ⇔ R1
  - A★ > 0 ⇔ R2
- **Non-normalized**: A = 0.5((1−p)+(1−κ)) + E

### Properties

1. **Normalization**: A★ = 0 in R1; grows when independence shrinks.
2. **Invariance**: stable under re-timing (geometry-neutral).
3. **Monotonicity**: enlarging independence ⇒ p↑, κ↑, E↓ ⇒ A★↓.

### Arithmetic Selection Rule

| Zone | A★ Range | Regime |
|------|----------|--------|
| Low | A★ ≲ 0.15 | (+,+) quasi-additive |
| Intermediate | 0.15 ≲ A★ ≲ 0.5 | Mixed: tropical for depth/distance, additive for cost |
| High | A★ ≳ 0.5 | Tropical and (+,max) dominant |

> Thresholds indicative; calibrate for context.

### Non-Exchange Cost

If residuation exists: δ_I(f,g) = I(g∘f) ▷ I(f⊗g); then δ_I ≡ 0 ⇔ A★ = 0 for invariant I.

### Practical Algorithm

```
Input: causal graph, independence relation, invariant I, set of pairs (f,g)

1) p := (# independent pairs) / (# total pairs)
2) κ := (# contexts where interchange holds | ⊗ defined) / (# tested contexts)
3) E_fg := |I(g∘f) − I(f⊗g)| / max(1, |I(g∘f)|, |I(f⊗g)|)
   Aggregate E (median or P95)
4) A★ := α(1−p) + β(1−κ) + γE
5) Choose regime based on A★; apply corresponding operators
```

---

## 12) Decision Policies for A★ — Discrete vs Continuous

### Discrete Threshold Policy

- **Parameters**: two thresholds θ₁ < θ₂.
- **Decision**:
  - (+,+) if A★ < θ₁
  - mixed if θ₁ ≤ A★ < θ₂
  - {(max,+), (min,+), (+,max)} according to invariant if A★ ≥ θ₂
- Thresholds can be set by quantiles, risk minimization, or domain rules.

### Continuous Mixture Policy

Smooth weights (mixture-of-experts):

```
w_add(A★) = exp(−λA★)
w_trop(A★) = 1 − w_add(A★)
```

Or general softmax.

Output: F(A★) = Σᵣ wᵣ(A★) · Fᵣ, r ∈ {max+, min+, ++, +max}.

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

### Result 3 — Proof/Decision Incompleteness (Conjecture)

**Conjecture**: The inequality logic generated by ⊗, ∘, and local interchange, valid for all independence relations, admits no finite, complete axiomatisation.

**Precise formulation needed**: Define the logic as:

- Signature: (⊗, ∘, ≤) with ⊗ partial
- Axiom schemes: interchange locality, unit laws, associativity
- Target: completeness relative to PCM-based semantics

**Reason**: interchange locality depends on the fine structure of independence; families (e.g., diamond lattices) require unbounded rule schemes.

### Role of A★ (Bridge)

- **A★ = 0**: ⊕ ≈ ⊙ → structural no-go disappears.
- **A★ > 0**: the four-host classification becomes necessary (Result 1), observation via (L,W,C,…) becomes insufficient (Result 2), and a finite global axiom base is unlikely (Result 3).

---

## To-Do

- [ ] Write full proof of Result 1 (idempotence/absorption).
- [ ] Record explicit counterexample for Result 2 (with R distinguishing).
- [ ] For Result 3: define the logic precisely, build a parametric family, and show non-finiteness (or relative completeness for restricted classes like series-parallel).

---
