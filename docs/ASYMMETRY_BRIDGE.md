# Asymmetry as a Bridge Between Two Reference Frames

## 0) Philosophy of Dissociation

### 0.1 The Primitive

Dissociation is the **ontological primitive** of this framework. It is the assertion:

> Certain things can be **separated** (disjoint supports) and composed in parallel. This separation is **partial**: not everything dissociates from everything.

Formally: a PCM (partial commutative monoid) $(S, \perp, \uplus, \varnothing)$ where $x \perp y$ (disjointness) conditions $x \uplus y$ (union). The parallel $\otimes$ exists only under disjointness. The sequential $\circ$ exists always.

**Dissociation is the fundamental asymmetry between $\otimes$ (conditional) and $\circ$ (total).** Everything else follows.

### 0.2 The Causal Cascade

The framework has a strict logical direction. Each arrow is a **theorem**, not a modeling choice:

```
Dissociation (PCM, ⊥)
    │
    │  engenders (§1, paper §3)
    ▼
Local interchange (2-cells)
    │
    │  constrains (paper §9, Thm 9.1)
    ▼
Four stable arithmetics (⊕,⊙)
    │
    │  projected by (paper §8, factorization)
    ▼
Invariants (L, W, C, d)
    │
    │  measured by (§2, projection hierarchy)
    ▼
Asymmetry A★_I_I_I(t) = projection of holonomy (Screening)
    │
    │  signals risk (Lean: lag_of_twist_and_hidden_step needs A★_I_I_H)
    ▼
Lag (invisible future divergence)
```

| Arrow | Theorem | Source |
|-------|---------|--------|
| Dissociation → interchange | Interchange is the natural law of the (⊗, ∘) square | Paper §3.2 |
| Interchange → 4 arithmetics | Classification: only (max,+), (min,+), (+,+), (+,max) survive | Paper Thm 9.1 |
| Arithmetics → invariants | Lax-monoidal factorization | Paper Thm 8 |
| Invariants → holonomy | Transport on fibers, HolonomyRel | Lean `HolonomyRel` |
| Holonomy → A★_I_I | Projection Sig → Hol → (p, κ_I, E_I) → A★_I_I | This document §2 |
| A★_I_I_H > 0 → lag | Twist + hidden-dependent step ⇒ lag event | Lean theorem (Strong) |
| A★_I_I_I > 0 → lag risk | Screening signal; requires Sep_I to imply A★_I_I_H > 0 | Interpretation |

### 0.3 Three Faces of Dissociation

Dissociation manifests at three levels, corresponding exactly to the Symmetry–Asymmetry–Dissymmetry trio:

**1) Dissociation as structure (the PCM).**
The brute fact: some pairs are independent, others are not. This is the relation ⊥(t). The paper calls it the "dissociation referential". It is **R2** in this document.

**2) Dissociation as measure (A★_I_I).**
The quantification of *how much* the system is dissociated relative to a fully parallelizable state. A★_I_I = 0 means "everything dissociates perfectly" (R1). A★_I_I > 0 means "dissociation is partial or imperfect". This is the **bridge** R1 ↔ R2.

> **Key subtlety**: A★_I_I = 0 does not mean "no dissociation". It means "**perfect** dissociation" — everything parallelizes, interchange holds everywhere. This is the maximal case of R2 that coincides with R1. The terminology is counter-intuitive at first: the better dissociation works, the lower A★_I_I.

**3) Dissociation as profile (dissymmetry).**
*How* dissociation manifests in the arithmetic: which pair (⊕,⊙) dominates. The paper shows the classification is canonical. This document shows the profile can change dynamically (R(t)).

### 0.4 Partialité de ⊗: The Engine

The entire machinery rests on **one fact**: $\otimes$ is partial, $\circ$ is total.

| Consequence of partial ⊗ | Formulation |
|--------------------------|-------------|
| Interchange is only **local** | Holds only where both parallels exist |
| Distributivity is only **lax** | ⊙ does not distribute globally over ⊕ |
| Holonomy can be **twisted** | Two paths (parallel-first vs series-first) give different results |
| Lag exists | Observationally identical micro-states diverge later |
| A★_I_I > 0 is possible | The system is not fully dissociated |
| Four arithmetics (not one) | Partiality prevents a universal structure (Result 1, no-go) |

If $\otimes$ were total (as in a classical symmetric monoidal category), **everything collapses**:

- Interchange would be global → exact distributivity → single semiring
- Holonomy would be flat → no lag → A★_I_I ≡ 0
- The paper would have one arithmetic, not four

### 0.5 Three Layers, One Phenomenon

| Layer | Document | Question answered | Dissociation appears as... |
|-------|----------|-------------------|---------------------------|
| Algebraic | Paper (doc 4) | Where does arithmetic come from? | The PCM + interchange that forces 4 pairs |
| Geometric | Lean (doc 3) | What happens when dissociation is imperfect? | Twisted holonomy, lag, obstruction |
| Calculable | This document | How to measure dynamically? | A★_I_I(t) trajectory, regime dynamics |

```
                    DISSOCIATION
                    (the primitive)
                         │
         ┌───────────────┼───────────────┐
         │               │               │
      Paper           Lean          This document
    "Where does     "What happens    "How to
     arithmetic      when it          measure"
     come from"      twists"
         │               │               │
    Classification   Holonomy,      A★_I_I(t),
    4 stable pairs   Lag, Gauge,    trajectories,
                     Obstruction    regimes
         │               │               │
         └───────────────┼───────────────┘
                         │
                    OPERATIONAL
                    CONSEQUENCES
```

### 0.6 What the Lean Adds to the Paper

The paper proves: "from dissociation emerge four arithmetics". But it does not say what happens **between** arithmetics, or what occurs when the system transitions from one to another. The Lean fills this gap:

- **The gauge** is the correction applied when the chosen arithmetic does not perfectly capture the actual dissociation. It is the "gauge choice" in the physics sense.
- **Obstruction** (`ObstructionWrt`) says: sometimes **no** correction suffices. The dissociation is structurally incompatible with repair. This is the paper's no-go (Result 1) made dynamic.
- **Cofinality** says: obstruction/repair has a **permanent** character — it persists in every future. It is not a local accident.

### 0.7 Dissociation in One Sentence Per Layer

| Layer | Dissociation is... |
|-------|--------------------|
| Ontological | The partiality of ⊗ (some things don't separate) |
| Algebraic | What forces four arithmetics to exist (not one) |
| Geometric | What allows twisted holonomy (two paths ≠ same result) |
| Dynamic | What makes A★_I_I(t) > 0 possible and lag real |
| Operational | What makes apparently identical systems diverge later |

These are five descriptions of the **same phenomenon**, linked by formal theorems.

---

## 1) Two Well-Defined Reference Frames

### R1 — Classical Frame of Symmetry

- **Setting**: an object X with a group of symmetries G (or a symmetric monoidal structure).
- **Symmetry**: invariance under G (or global factor exchange).
- **Classical asymmetry**: deviation from invariance (symmetry breaking, non-commutativity, non-invariance).

### R2 — Frame of Dissociation

- **Setting**: a time-varying independence relation ⊥(t) conditioning a partial parallel (⊗), defined only if f ⊥(t) g, a sequential (∘), and a local interchange.

- **Measures (I)**:
  - Parallel induces a parallel aggregation (⊕) via I(f ⊗ g) = I(f) ⊕ I(g) (when defined at time t).
  - Series induces a serial aggregation (⊙) via I(g ∘ f) ≽ I(g) ⊙ I(f) (subadditivity).

- **Classification**: only four stable arithmetics appear: (max,+), (min,+), (+,+), (+,max).

  > **Note**: Only (max,+) and (min,+) are semirings. (+,+) and (+,max) satisfy the weaker local interchange axiom but not global distributivity. "Arithmetic" means (⊕,⊙) satisfying H1–H2, not necessarily a semiring.

- **Geometric neutrality**: only precedences (pomset) matter, not drawing or layout.

- **Temporal reading**: R2 is not a fixed alternative to R1 — it is what R1 **becomes** when independence is restricted (§0.3). A system can move from R1 to R2 (dissociation degrades) and back (resynchronization) over time.

### Formal Backbone

| Layer | Formal (Lean) | Calculable (this document) | Algebraic (paper) |
|-------|---------------|---------------------------|--------------------|
| Objects | Prefixes `P` | States / configurations | Supports in PCM |
| 1-morphisms | `Path h k` | Orderings of tasks | Morphisms in 𝐂_ℱ |
| 2-morphisms | `Deformation p q` | Interchange squares | Interchange law |
| Semantics | `sem : Path → Relation S S` | Invariant I : configs → ℝ | I satisfying (i)–(iv) |
| Fibers | `FiberPt obs target_obs h` | Micro-states with same obs | Observation Obs : Hom → V |
| Independence | Which ⊗ are defined | ⊥(t) | PCM disjointness ⊥ |

---

## 2) Asymmetry as a Dynamic Bridge Between R1 and R2

### Core Idea

The system evolves. At each time t:

- The causal graph G(t) determines available tasks and precedences.
- The independence relation ⊥(t) determines which pairs can be parallelized.
- The invariant I and arithmetic (⊕,⊙) determine how measurements aggregate.

Asymmetry is not a static label — it is a **trajectory** through the space of independence structures. It measures how far the system is from perfect dissociation (§0.3, face 2).

### Instantaneous Observables

All observables are functions of time through ⊥(t) and G(t).

- **Parallelizability** p(t) ∈ [0,1] — proportion of pairs independent at time t. Measures how much of the PCM structure is "active".

- **Interchange locality** κ_I(t) ∈ [0,1] — fraction of interchange squares where

  ```
  I((f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)) = I((f₁ ∘ f₀) ⊗ (g₁ ∘ g₀))
  ```

  holds at time t, conditional on both parallels being defined.

  > Each interchange test requires a **square** (f₀, f₁, g₀, g₁) with f₀ ⊥(t) g₀ and f₁ ⊥(t) g₁. This is a `Deformation` (2-cell) in the history graph, and corresponds to the interchange law in paper §3.2.

- **Interchange defect** E_I(t) ∈ [0,1) — quantitative amplitude of interchange failure at time t.

  For a square at time t:

  ```
  p_sq = (f₁ ⊗ g₁) ∘ (f₀ ⊗ g₀)      (parallel-first)
  q_sq = (f₁ ∘ f₀) ⊗ (g₁ ∘ g₀)      (series-first)
  ```

  **Pointwise defect**:

  ```
  E_I(f₀,f₁,g₀,g₁; t) = |I(p_sq) − I(q_sq)| / (1 + |I(p_sq)| + |I(q_sq)|)
  ```

  **Aggregate**: E_I(t) = median or P95 over all squares available at time t.

### The Complete Invariant and Its Projections

The observables (p, κ_I, E_I) are **not** the ground truth. The formal structure provides a richer object:

**Compatibility signature** (Lean: `Sig`). For a micro-state x in fiber F(h) at time t:

```
Sig(x, t) : Future(h) → {true, false}
Sig(x, t)(step) = "∃ y in fiber F(k) such that Transport(step) relates x to y"
```

Complete invariant for future prediction (Lean: `sig_iff_of_summary_correct`).

**Holonomy relation** (Lean: `HolonomyRel`). For a 2-cell α : p ⇒ q:

```
Hol(α)(x, x') ⇔ ∃ y ∈ F(k), Transport(p)(x,y) ∧ Transport(q)(x',y)
```

A relation on fibers, not a number.

**The projection hierarchy**:

```
Sig(x,t) ──complete──→ Hol(α) ──per-cell──→ (κ_I, E_I) ──aggregate──→ A★_I_I(t)
   ↑                      ↑                      ↑                      ↑
 function              relation               scalars               scalar
 on futures           on fiber pairs          per square            global index
```

Each arrow loses information. The document works at the rightmost level (A★_I_I) for computability.

---

## (P0) Two Levels: Holonomy (Relational) vs Invariant (Scalar)

There are **two distinct levels**:

1. **Holonomic Level (Lean)**: the primitive fact is the holonomy relation
   $$ \mathrm{Hol}(\alpha) \subseteq F(h) \times F(h) $$
   for each 2-cell $\alpha: p \Rightarrow q$.
   The intrinsic notion is:
   - **FlatHolonomy**: $\mathrm{Hol}(\alpha) \subseteq \Delta$ (diagonal).
   - **TwistedHolonomy**: $\exists x \neq x'$ with $\mathrm{Hol}(\alpha)(x,x')$.

2. **Calculable Level (Scalar)**: we observe an invariant $I$ (or an observable that $I$ factorizes) and measure **numerical defects** on interchange squares.

**Key Principle**: an invariant can be **blind** to a holonomic twist. Thus "no measured defect" does not imply "no twist" without a separability hypothesis.

### (P1) Separability Hypothesis / Invariant Fidelity

We introduce the following hypothesis, explicitly when lifting from scalar to holonomy:

**(Sep_I)** *(Separability / Summary-Correctness relative to observable)*
The invariant $I$ (or the summary $I$ depends on) is **sufficiently faithful** to detect relevant holonomic torsion: if two micro-states $(x,x')$ have incompatible futures (in the sense of $\mathrm{Sig}$), then the observation inducing $I$ separates them.

> Reading: (Sep_I) = "the scalar does not confound causally diverging states".

Without (Sep_I), $I$ remains a **proxy** (screening), not a decider.

### (P2) Two Indices: $A^\star_H$ (Intrinsic) and $A^\star_I$ (Calculable)

#### (P2.1) Holonomic Index (Intrinsic)

Defined **directly** from 2-cells and $\mathrm{Hol}$ (Lean level).

- $\kappa_H(t)$: fraction of 2-cells $\alpha$ at time $t$ such that $\mathrm{Hol}(\alpha) \subseteq \Delta$.
- $E_H(t)$: aggregated intensity of torsion (e.g., proportion of pairs $x \neq x'$ in linked fibers, or admissible relational norm).

$$ A^\star_H(t) = \alpha(1-p(t)) + \beta(1-\kappa_H(t)) + \gamma E_H(t) $$

**Property**: $A^\star_H(t) = 0 \iff$ flat holonomy on all 2-cells at $t$.

#### (P2.2) Invariant Index (Calculable)

We keep the calculable index:

- $\kappa_I(t)$ = fraction of squares where $I(p_{sq}) = I(q_{sq})$.
- $E_I(t)$ = median/P95 of $\frac{|I(p_{sq})-I(q_{sq})|}{1+|I(p_{sq})|+|I(q_{sq})|}$.

$$ A^\star_I(t) = \alpha(1-p(t)) + \beta(1-\kappa_I(t)) + \gamma E_I(t) $$

**Status**: $A^\star_I$ is a **calculable summary**, depending on the choice of $I$.

---

### Dynamic Index (Invariant / Screening)

```
A★_I(t) = α(1 − p(t)) + β(1 − κ_I(t)) + γ E_I(t)
```

with **α, β, γ > 0** and α + β + γ = 1.

- **A★_I(t) = 0** ⇔ p(t) = 1, κ_I(t) = 1, E_I(t) = 0.
- **A★_I(t) → 1** ⇔ p(t) → 0, κ_I(t) → 0, E_I(t) → 1.

> **Reading A★_I(t) = 0**:
>
> - If **(Sep_I)** holds, implies **FlatHolonomy** (perfect dissociation).
> - Without (Sep_I), implies **I-flatness**: the invariant sees no twist.

### Convention When p(t) = 0

**Penalty convention** (recommended for trajectories): κ_I(t) := 0, E_I(t) := 1.

- Absence of independence = maximal constraint. A★_I_I(t) = 1.
- Formal justification: aligns with `ObstructionWrt` under `GaugeRefl` (§6.2).

**Neutral convention** (analytic convenience): κ_I(t) := 1, E_I(t) := 0. A★_I_I(t) = α.

- Formal justification: `AutoRegulated` is vacuously true when no 2-cells exist.

### Trajectory Semantics

A★_I_I(·) : T → [0,1] encodes movement between frames:

- **A★_I_I(t) increasing**: dissociation degrading — independence shrinking, interchange failing.
- **A★_I_I(t) decreasing**: resynchronizing — independence expanding, interchange improving.
- **A★_I_I(t) ≈ const**: stable regime.

Derivative: ΔA★_I_I(t) = A★_I_I(t + dt) − A★_I_I(t). Sign encodes direction.

---

## 3) The Holonomy–Lag–Trajectory Bridge

The chain connecting formal structure to operational consequences:

```
Twisted holonomy at t  →  Lag event at t' > t  →  A★_I_I > 0  →  regime sensitivity
```

### 3.1 Holonomy Twist → Lag

**TwistedHolonomy ⇒ Lag**:

- **Strong implication (Intrinsic)**:
  $$ A^\star_H(t) > 0 \wedge \text{StepDependsOnHidden} \Rightarrow \exists \text{LagEvent} $$
- **Screening implication (Invariant)**:
  $$ A^\star_I(t) > 0 \Rightarrow \text{"risk of lag"} $$
  $$ (Sep_I) \wedge A^\star_I(t) > 0 \wedge \text{StepDependsOnHidden} \Rightarrow \exists \text{LagEvent} $$

**Connection to dissociation** (§0.4): the lag exists **because** ⊗ is partial. If ⊗ were total, holonomy would be flat, and no lag could occur.

> **Operational meaning**: A★_I_I > 0 means there exist micro-states that **look the same now** but **behave differently later**. Any controller ignoring A★_I_I risks wrong decisions.

### 3.2 Lag → Trajectory Consequences

- **Immediate**: prediction at t fails at t' > t.
- **Cascading**: wrong micro-state generates further wrong predictions.
- **Statistical**: repeated lag events appear as unexplained variance.

**Lag density**: λ_lag(t) = (# lag events from cells at t) / (# cells at t).

- A★_H(t) = 0 ⇒ λ_lag(t) = 0 (flat holonomy, no lag).
- A★_I(t) > 0 is a screening flag: it indicates potential twist for the chosen invariant I. To conclude existence of lag, one needs (Sep_I) to lift A★_I(t) > 0 to A★_H(t) > 0, plus a hidden-dependent step.

### 3.3 Information Loss in the Projection

| Level | Captures | Loses |
|-------|----------|-------|
| Sig(x,t) | Complete future behavior | Nothing |
| Hol(α) | Fiber confusion per 2-cell | Which steps are affected |
| (κ_I, E_I) | Rate and amplitude | Which cells twist |
| A★_I_I(t) | Global index | Distinction between p, κ_I, E_I |

A★_I_I is a **screening tool**: A★_I_I = 0 reliably means "no problem" (under Sep_I). A★_I_I > 0 means "investigate".

### 3.4 The Summary Separation Theorem

Any correct 1D predictor of compatibility must separate micro-states with different futures (Lean: `summary_separates_compatible_witness`). Applied to observation-only summaries: since x, x' share the same fiber, σ(x) = σ(x') always. Therefore **no observation-only summary predicts the lag** (Lean: `lagEvent_gives_summary_witness`).

This is the formal reason A★_I_I matters: lag is invisible to the observable.

---

## 4) Axioms as Trajectory Properties

| Axiom | Type | Statement | Formal anchor |
|-------|------|-----------|---------------|
| 1. Normalization | Pointwise | A★_I_I_H(t)=0 ⇔ flat holonomy | `FlatHolonomy` |
| 2. Re-timing | Pointwise | Invariant under pomset-preserving transforms | Geometric neutrality |
| 3. Monotonicity | Path | ⊥ expanding + interchange-preserving ⇒ A★_I_I ↓ | ⊥(t₁) ⊆ ⊥(t₂) |
| 4. Geometric neutrality | Pointwise | Representation-independent | Paper §7 |
| 5. Directional semantics | Trajectory | ΔA★_I_I > 0 ↔ dissociation degrading | Sign of derivative |
| 6. Lag coupling | Causal | A★_I_I_H > 0 + hidden-dep step ⇒ ∃ lag | `lag_of_twist_and_hidden_step` |

**Axiom 3 caveat**: κ_I is a conditional ratio. Adding squares that fail interchange can decrease κ_I. Monotonicity requires new pairs to satisfy interchange at rate ≥ κ_I(t₁).

---

## 5) Regime Dynamics

### 5.1 The Regime as a Gauge

In the formal layer, a **gauge** (Lean: `Gauge`) is a fiber-preserving correction:

```
φ : Path h k → Relation (Fiber(k)) (Fiber(k))
```

In the calculable layer, the **regime choice** R(t) plays the gauge role:

- Choosing (⊕,⊙) determines how I aggregates ⇒ determines Transport.
- Wrong regime = non-admissible gauge: corrected holonomy not diagonal.
- Right regime = gauge making corrected holonomy closest to diagonal.

**Connection to paper**: The four arithmetics (paper Thm 9.1) are the four **canonical gauges** emerging from the dissociation structure. Each is optimal for a different invariant (L, W, C, d).

### 5.2 Admissibility: GaugeRefl

- **GaugeRefl**: φ contains the diagonal. Can only add possibilities, never remove.
- **emptyGauge**: trivially makes holonomy empty — vacuously diagonal but operationally useless.

GaugeRefl blocks this: pre-existing twist **persists** after correction (Lean: `correctedHolonomy_of_holonomy_of_gaugeRefl`). A twist cannot be gauged away.

**In A★_I_I terms**: penalty convention = requiring GaugeRefl. Prevents A★_I_I from collapsing via vacuity.

### 5.3 Regime as Stateful Process

```
R(t) = Policy(A★_I_I(t), R(t⁻), ΔA★_I_I(t), invariant)
```

### 5.4 Transition Dynamics

**Memoryless**: R(t) = σ(A★_I_I(t)).

**Hysteretic**: activate at θ_on, deactivate at θ_off < θ_on (dead zone).

**Anticipatory**: in gray zone, use sign of ΔA★_I_I to pre-switch or hold.

### 5.5 Cofinal Auto-Regulation

`AutoRegulatedCofinal` (Lean): ∃ cofinal C such that one gauge repairs all cells over C.

In trajectory terms: ∃ horizon T₀ such that ∀ t > T₀ in C, A★_I_I(t) = 0 under the chosen gauge.

If this fails (`ObstructionCofinalWrt`): **permanent twist**. No regime eliminates the lag in any cofinal future. This is the paper's no-go (Result 1) made temporal.

### 5.6 Phase Portrait

```
         ΔA★_I_I(t)
           ↑
    +0.5   |   Pre-switch              Deep R2, worsening
           |   (lag risk rising)        (lag likely)
           |
   ────────┼───────────────────────────────→ A★_I_I(t)
           |        0.15        0.5
           |
    −0.5   |   Returning to R1         Partial recovery
           |   (lag risk falling)       (lag decreasing)
```

| A★_I_I(t) | ΔA★_I_I(t) | Lag risk | Action |
|-------|--------|----------|--------|
| < 0.15 | any | Negligible | All regimes equivalent |
| 0.15–0.5 | > 0 | Rising | Pre-switch |
| 0.15–0.5 | ≤ 0 | Falling | Hold |
| > 0.5 | > 0 | High, worsening | Locked; monitor |
| > 0.5 | < 0 | High, improving | Hold; evaluate downshift |

### 5.7 Residence Statistics

```
τ_{R1}/T,  τ_{R2}/T,  ν (transition rate),  ⟨A★_I_I⟩,  σ_A (volatility),  ⟨λ_lag⟩
```

---

## 6) Symmetry – Asymmetry – Dissymmetry (Dynamic Trio)

The three faces of dissociation (§0.3) made dynamic:

- **Symmetry (R1)**: p(t) = 1, κ_H(t) = 1, E_H(t) = 0. Perfect dissociation. Flat holonomy implies regime insensitivity: any two 2-equivalent histories yield identical predictions for the relevant observable; no lag is possible. Regime choice becomes a convention rather than a necessity.

- **Asymmetry (bridge)**: trajectory A★_I_I(t). Measures how far dissociation is from perfect. A★_I_I > 0 = twist exists = lag possible = regimes diverge.

- **Dissymmetry (profile)**: R(t) ∈ {(max,+), (min,+), (+,+), (+,max)}. Which arithmetic dominates. Can change along trajectory. The profile is **orthogonal** to A★_I_I: a system can have A★_I_I = 0 in any regime.

---

## 7) Structural Statements (Formal Anchoring)

| Statement | Content | Formal anchor |
|-----------|---------|---------------|
| **L1** Symmetric limit | A★_I_I_H(t)=0 ⇔ FlatHolonomy. A★_I_I_I(t)=0 ⇒ I-flatness (impl FlatHol under Sep_I) | `FlatHolonomy` |
| **L2** Host factorization | Any stable invariant I (H1–H4) induces one of four hosts. When A★_H(t) > 0, the choice becomes sensitive (wrong host ≈ wrong gauge). | Paper Thm 8, 9.1 |
| **L3** Non-exchange cost | δ_I ≡ 0 ∧ p=1 ⇔ A★_I_I=0 (vacuity caveat when p=0) | `HolonomyRel` |
| **L4** Geometric neutrality | A★_I_I invariant under pomset-preserving transforms | Paper §7 |
| **L5** Dissociation direction | ⊥ shrinking ⇒ A★_I_I increasing | Axiom 3 contrapositive |
| **L6** Lag coupling | A★_I_I_H>0 + hidden-dep step ⇒ ∃ lag event. A★_I_I_I>0 is a signal. | `lag_of_twist_and_hidden_step` |
| **L7** Observation insufficiency | No obs-only summary predicts lag | `lagEvent_gives_summary_witness` |
| **L8** Gauge irreparability | TwistedHolonomy + GaugeRefl ⇒ ObstructionWrt | `obstructionWrt_singleton_of_...` |

---

## 8) Quick Numerical Example (Dynamic)

### Setup

Four tasks: f₀ = 2, f₁ = 3, g₀ = 1, g₁ = 4. Invariant: L (makespan) in (max,+).

### Phase 1 (t = 0): partial independence

Six pairs, two independent → p(0) = 1/3.

```
p_sq = max(3,4) + max(2,1) = 6    (parallel-first)
q_sq = max(3+2, 4+1) = 5          (series-first)
```

κ_I(0) = 0, E_I(0) = 1/12 ≈ 0.083. A★_I_I(0) = **0.583** (penalty).

**Dissociation reading**: the PCM allows (f₀, g₀) and (f₁, g₁) to dissociate, but the interchange fails — the way tasks combine depends on the scheduling order. This is the **partialité de ⊗** manifesting through the invariant.

### Phase 2 (t = 1): conflict

f₁ ⊥̸ g₁ → p(1) = 1/6. No square. Penalty: κ_I := 0, E_I := 1. A★_I_I(1) = **0.944**.

**Dissociation reading**: the PCM structure has shrunk. A pair that could dissociate no longer can. The system moves deeper into R2.

### Phase 3 (t = 2): conflict resolved

Same as Phase 1 → A★_I_I(2) = **0.583**.

**Dissociation reading**: the PCM expands back. The system resynchronizes.

### Trajectory

```
A★_I_I: 0.583 ──→ 0.944 ──→ 0.583
         ↑ dissociation    ↓ resynchronization
         degrading         restoring
```

### Interchange failure: why it's structural

```
max(f₁,g₁) + max(f₀,g₀) ≠ max(f₁+f₀, g₁+g₀)
```

when dominance switches lanes. This is the scalar shadow of `TwistedHolonomy` — two schedulings of the same dissociated tasks produce different results. The twist exists **because** ⊗ is partial (§0.4).

---

## 9) Dictionary

| Term | Definition |
|------|-----------|
| **Dissociation** | The partiality of ⊗; the primitive that generates the framework |
| **Asymmetry (classical)** | Lack of invariance under a symmetry group |
| **Asymmetry (dissociative)** | A★_I_I(t): trajectory measuring departure from perfect dissociation |
| **Dissymmetry** | Arithmetic profile R(t); how the twist manifests |
| **Lag** | Delayed divergence of observationally identical micro-states |
| **Gauge** | Fiber-preserving correction; the regime choice is an implicit gauge |
| **Obstruction** | Twist that no admissible gauge can repair |

---

## 10) Bounds and Normalization

- **Minimal**: A★_I_I(t) = 0 when p=1, κ_I=1, E_I=0 (perfect dissociation).
- **Maximal**: A★_I_I(t) = 1 under penalty convention when p=0 (no dissociation).
- **Weights** α, β, γ > 0 tune importance. Can be time-varying.

---

## 11) Effect of A★_I_I on the Four Arithmetics

### 11.1 Sensitivity

- A★_I_I ≈ 0: all four arithmetics agree (flat holonomy). Regime = convention.
- A★_I_I moderate: regimes diverge on some cells. Regime matters.
- A★_I_I ≈ 1: regimes diverge strongly. Wrong regime = unrepaired twist = lag.

### 11.2 Linking Regimes

- (max,+) ↔ (min,+) by order reversal. (+,+) self-dual. (+,max) no simple dual.
- LogSumExp: max ≤ (1/β)log(Σeᵝˣ) ≤ max + (log n)/β. Max is lower bound.
- Residuation: numeric in (max,+), (min,+), (+,+); implicative in (+,max).

### 11.3 Universal Bounds

C₊₊ ≥ L_{max+}, C₊₊ ≥ d_{min+}, C₊₊ ≥ W_{+max} (antichains are subsets).

### 11.4 Arithmetic as Gauge

| Arithmetic | Gauge selects... | Optimal when... |
|-----------|-----------------|-----------------|
| (max,+) | Critical path (max) | Bottleneck dominates |
| (min,+) | Shortest path (min) | Distance/risk |
| (+,+) | Total sum | All contributions equal |
| (+,max) | Max of parallel sums | Width/bandwidth |

Wrong arithmetic when A★ > 0 = non-GaugeRefl gauge: masks twist or introduces artifacts.

---

## 12) Q-Symmetry (QSym) — Dynamic Quantified Bridge

### Definition

- **Triplet**: QSym(t) = (p(t), κ_I(t), E_I(t)).
- **Index**: A★(t) = α(1−p) + β(1−κ_I) + γE_I.
- **Velocity**: ΔA★(t).
- **State**: S(t) = (A★(t), R(t), ΔA★(t)).
- **Anchor**: A★ is 1D projection of holonomy; QSym is 3D projection.

### Trajectory Classification

| Pattern | Name | Dissociation reading |
|---------|------|---------------------|
| A★ ≈ 0 stable | Symmetric equilibrium | Perfect dissociation maintained |
| A★ ≈ c > 0 stable | Dissociated equilibrium | Stable partial dissociation |
| A★ increasing | Dissociation degrading | ⊥(t) shrinking |
| A★ decreasing | Resynchronizing | ⊥(t) expanding |
| A★ oscillating | Regime cycling | Independence/conflicts alternate |
| A★ spike/return | Transient disruption | Temporary conflict, self-healing |

### Practical Algorithm

```
Input: time-varying G(t), ⊥(t), invariant I, arithmetic (⊕,⊙),
       observation times {t₁, …, t_N}

For each tₖ:
  1) p(tₖ) := (# independent pairs) / (# total pairs)
  2) Enumerate interchange squares S(tₖ)
     If |S(tₖ)| = 0:
       Penalty: κ_I := 0, E_I := 1
       Neutral: κ_I := 1, E_I := 0
  3) Else:
       For each square, compute defect
       κ_I(tₖ) := (# successes) / |S(tₖ)|
       E_I(tₖ) := median(defect)
  4) A★(tₖ) := α(1−p) + β(1−κ_I) + γE_I
  5) ΔA★(tₖ) := A★(tₖ) − A★(tₖ₋₁)
  6) R(tₖ) := Policy(A★(tₖ), R(tₖ₋₁), ΔA★(tₖ), invariant)

Output: A★(·), R(·), ΔA★(·); residence statistics; lag density.
```

---

## 13) Decision Policies

### 13.1 Static

R(t) = σ(A★(t)) via thresholds θ₁ < θ₂.

### 13.2 Hysteretic

Activate at θ_on, deactivate at θ_off < θ_on.

### 13.3 Anticipatory

In gray zone: ΔA★ > +ε → pre-switch; ΔA★ < −ε → hold.

### 13.4 Continuous Mixture

Two-regime: w_add = exp(−λA★), w_trop = 1 − w_add.

Four-regime: softmax w_r(A★) = exp(s_r(A★)) / Σ exp(s_{r'}).

### 13.5 Adaptive Weights

α(t) = α₀ + α₁ · Var(p)_{[t−W,t]}. Renormalize.

### 13.6 Gauge Admissibility as Policy Constraint

Any reasonable policy must correspond to a GaugeRefl-admissible gauge:

- Must not delete states (no emptyGauge).
- Must not claim A★ = 0 when twist exists.
- If `ObstructionWrt(GaugeRefl, J)`: no policy reduces A★ to 0 on J. The twist is real.

---

## 14) Incompleteness Results

### Result 1 — Structural (no-go)

No scalar arithmetic is simultaneously tropical and additive (idempotent ⊕ + absorbing 𝟘 vs not).

**Dissociation reading**: the four arithmetics are **necessary** because the dissociation structure (partial ⊗) prevents a universal algebra (§0.4). A system crossing regimes must switch.

### Result 2 — Observational

Non-isomorphic pomsets can share identical (L, W, C). Scalar invariants don't capture full holonomy.

**Dissociation reading**: the projection Hol → (L, W, C) loses the fine structure of how dissociation interacts with scheduling.

### Conjecture 1 — Axiom Incompleteness (Open)

The inequality logic of (⊗, ∘, local interchange) likely admits no finite complete axiomatisation.

**Dissociation reading**: the partiality of ⊗ makes the logic depend on the fine structure of ⊥, which varies unboundedly.

---

## 15) TL;DR

- **Dissociation** (partiality of ⊗) is the primitive. Everything derives from it.
- **Four arithmetics** emerge canonically from dissociation + interchange.
- **Asymmetry** A★(t) measures departure from perfect dissociation — a trajectory, not a label.
- **A★ = 0**: perfect dissociation, flat holonomy, no lag, all regimes agree.
- **A★ > 0**: imperfect dissociation, twisted holonomy, lag possible, regime choice matters.
- **Lag** is the operational cost: identical-looking states diverge later. Invisible to observation.
- **Regime** = implicit gauge. GaugeRefl prevents vacuous repair.
- **Permanent obstructions** mean some twists cannot be gauged away.
- **A★ is lossy**: Sig → Hol → (p, κ_I, E_I) → A★. Screens; doesn't diagnose.

---

## Summary of All Corrections (v1 → v6)

### v5 → v6

| # | Change |
|---|--------|
| 1 | §0 "Philosophy of Dissociation": primitive, cascade, three faces, engine thesis |
| 2 | Partialité de ⊗ identified as the single generating fact |
| 3 | Five-layer table (ontological → operational) of dissociation |
| 4 | Paper integration: cascade arrows linked to specific theorems |
| 5 | Three-document architecture diagram |
| 6 | §0.6: what Lean adds to paper (gauge, obstruction, cofinality) |
| 7 | Dissociation readings added to example phases, structural statements, incompleteness |
| 8 | Dictionary expanded with dissociation-centric definitions |
| 9 | Arithmetic-as-gauge table (§11.4) with optimality conditions |

### v4 → v5 (formal integration, retained)

| # | Change |
|---|--------|
| 10 | Formal backbone table |
| 11 | Projection hierarchy Sig → Hol → (κ,E) → A★ |
| 12 | Non-reducibility theorem |
| 13 | Holonomy–Lag–Trajectory bridge (§3) |
| 14 | Summary separation theorem |
| 15 | Regime = gauge + GaugeRefl admissibility |
| 16 | L6, L7, L8 structural statements |
| 17 | Lag coupling axiom |

### v3 → v4 (dynamic, retained)

| # | Change |
|---|--------|
| 18 | All observables temporal |
| 19 | Axioms: pointwise vs path |
| 20 | Regime as stateful process |
| 21 | Phase portrait |
| 22 | Residence statistics |
| 23 | Penalty convention for trajectories |

### v2 → v3 (conceptual, retained)

| # | Change |
|---|--------|
| 24 | E → E_I (interchange defect) |
| 25 | A★=0 ≠ ⊕≈⊙ |
| 26 | 4-morphism example |
| 27 | Dissymmetry decoupled from A★ |

### v1 → v2 (technical, retained)

| # | Change |
|---|--------|
| 28 | α,β,γ > 0 |
| 29 | κ_I monotonicity conditional |
| 30 | L3 biconditional fixed |
| 31 | C₊₊ ≥ W justified |
| 32 | Two vs four mixture |
| 33 | Result 3 → Conjecture 1 |
| 34 | (+,+), (+,max) not semirings |

---

## To-Do

- [ ] Full proof of Result 1.
- [ ] Counterexample for Result 2 with R distinguishing.
- [ ] Conjecture 1: logic, parametric family, non-finiteness.
- [ ] κ_I monotonicity conditions.
- [ ] E_I aggregation (median vs P95) effect on phase portrait.
- [ ] Worked (+,+) example with A★ = 0.
- [ ] Penalty vs neutral convention as functor property.
- [ ] A★(t) as stochastic process.
- [ ] Implementation on scheduling/concurrency benchmarks.
- [ ] Formalize "regime = gauge" in Lean.
- [ ] Quantify projection hierarchy information loss.
- [ ] LagDensity formalization → ObstructionCofinalWrt.
- [ ] Connect paper's (ΔL, ΔW, ΔR) diagnostics to A★ trajectory.
- [ ] Explicit bridge: paper's Thm 9.1 classification ↔ doc's four regimes ↔ Lean's four possible gauge families.

---

## 16) Relative Primality (A Note on Factorization)

Primality is no longer an absolute property of an object-number, but a property **relative to the dissociation regime** (time-dependent independence).

- **Atom at time t**: x is independent-atomic at t if
    `x = y ∪ z` with `y ⊥(t) z` implies `y = empty` or `z = empty`.
    (Indecomposable in "admissible parallel".)

- **Divisibility at t**: `a |(t) b` means there exists c such that `b = a ∪ c` with `a ⊥(t) c`.

- **Prime at t**: If `a |(t) (b ∪ c)` implies `a |(t) b` or `a |(t) c`.

**Conclusion**: "Prime" is a dynamic status. An element can be prime (indecomposable) under strict dissociation, then composite when dissociation relaxes. This reflects the evolutionary nature of the PCM structure.
