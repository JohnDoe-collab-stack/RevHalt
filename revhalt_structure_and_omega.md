# RevHalt — Structure and Formal Grounding (Synthetic Reference)

This document provides a **structured reading** of RevHalt's global dynamics (5 axes) and explicates the **formal grounding** of the **Ω (OmegaChaitin)** instance via its **discrete** (bits) and **continuous** (rational cuts) primitives, as well as their **arithmetic bridge**.

---

## Contextual Mini-Glossary

*   **`OmegaModel`**: Time index `t` (often aliased to `ℕ` in implementation) used as local model.
*   **`OmegaApprox t`**: Computable rational approximation of Ω at time `t` (partial sum of weights of programs halting before `t`).
*   **`OmegaSat t φ`**: Local satisfaction relation; is property `φ` verified at time `t` by the current approximation?
*   **`LR_omega`**: *Local Reading*, the trace (sequence of booleans over time) monitoring validity evolution of a formula.
*   **`Kit`**: Abstract observation mechanism transforming a dynamic trace into a limit binary verdict.
*   **`pathCost`**: Trajectory cost in the moves graph (number of dynamic steps), not the length of a logical proof.

---

## Part 1 — The 5 Structural Axes of Global Dynamics

### Axis 1 — Incompleteness Engine (Fuel)

* **Pivot**: `fuel_from_T2`
* **File**: `RevHalt/Dynamics/Core/Fuel.lean`
* **Structural role**: Incompleteness is modeled as a **dynamic energy** (fuel) that forces perpetual extension of the system, rather than as a simple static barrier.

### Axis 2 — Observation Canonicity

* **Pivot**: `T1_traces`
* **File**: `RevHalt/Theory/Canonicity.lean`
* **Structural role**: Halting (`Halts`) is established as the **universal signature** of truth, robust with respect to variations in the observation mechanism (*Kit*).
    *   *Precision*: `T1_traces` shows that, for any class of admissible kits (satisfying `DetectsMonotone`), the limit verdict depends solely on the halting property of the trace (and coincides with `Halts` in the considered framework).

### Axis 3 — Kinetic Truth

* **Pivot**: `Master_Closure`
* **File**: `RevHalt/Kinetic/MasterClosure.lean`
* **Structural role**: Truth is defined as an **inductive limit** (*Closure*) of a stratification process, rather than a pre-existing static set.
    *   *Precision*: The *Closure* is the smallest set of sentences containing the base and closed under RevHalt's dynamic rules (moves / fuel-extension).

### Axis 4 — Turing–Gödel Unification

* **Pivot**: `T2_impossibility`
* **File**: `RevHalt/Theory/Impossibility.lean`
* **Structural role**: Undecidability (Turing) and incompleteness (Gödel) are formulated as two faces of a **single structural impossibility**: absence of an internal halting predicate that is simultaneously **total / correct / complete**.

### Axis 5 — Cost / Information Duality

* **Pivot**: `cost_ge_info_gain`
* **File**: `RevHalt/Dynamics/Core/Complexity.lean`
* **Structural role**: Every emergence of truth (information gain) admits a **certifiable cost** (`pathCost`). The cost bounds information gain via an **explicit witness** (a path of moves).

---

## Part 2 — OmegaChaitin Formal Grounding (Discrete / Continuous)

**Target file**: `RevHalt/Dynamics/Instances/OmegaChaitin.lean`
Object: Implementation of the inverted hierarchy for Ω via `OmegaSentence`.

---

### 2.1 Discrete Primitive — Ω Bit

* **Concept**: Discrete coordinate (bit)
* **Lean**: `OmegaBit` / `OmegaSentence.BitIs`
* **Immediate dependencies**: `OmegaSentence`, `OmegaReferent`

```lean
inductive OmegaSentence
| BitIs (n : ℕ) (a : Fin 2) : OmegaSentence
| WinDyad (n : ℕ) (a : Fin 2) : OmegaSentence
...

def OmegaBit (n : ℕ) (a : Fin 2) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.BitIs n a
```
*Note*: The `Fin 2` typing directly enforces that `a` is a bit (0 or 1).

### 2.2 Continuous Primitive — Rational Cut

* **Concept**: Continuous rational coordinate (cut)
* **Lean**: `OmegaCut` / `OmegaSentence.CutGe`
* **Immediate dependencies**: `OmegaSentence`, `Rat` (ℚ)

```lean
inductive OmegaSentence
| CutGe (q : ℚ) : OmegaSentence
...

def OmegaCut (q : ℚ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.CutGe q
```

---

### 2.3 Inverted Hierarchy (Cuts/Bits Asymmetry)

* **Standard (classical)**: bits (base) → real (derived)
* **RevHalt**: **Semi-decidable cuts** (base / primitives) → **Undecidable bits** (reconstructed / derived).
* **Semi-decidability grounding**: `namespace CutComputable`

**Explicit**: The system takes `CutGe q` predicates as primitives, which are semi-decidable (robust via `OmegaApprox`), and **reconstructs** bits as derived properties (window intersections).

Asymmetry excerpt:

```lean
theorem cut_semidecidable_bit_not (n : ℕ) :
    (∀ q, Halts (LR_omega ∅ (OmegaSentence.CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q)) ∧
    (∀ a : Fin 2, Halts (LR_omega ∅ (OmegaSentence.BitIs n a)) →
          ∃ t, (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = (a : ℕ))
```

*Reading*: `Halts (LR_omega ... (CutGe q))` characterizes `OmegaApprox ≥ q` (one can wait for the event, it's semi-decidable). For bits, there is no uniform halting procedure guaranteeing to decide the bit without additional information (typically, one must "guess" the right bit).

---

### 2.4 Discrete / Continuous Link — Dyadic Window Equivalence

* **Pivot**: `omega_bit_cut_link`
* **File**: `RevHalt/Dynamics/Instances/OmegaChaitin.lean`

```lean
theorem omega_bit_cut_link : ∀ {t : OmegaModel} {n : ℕ} {a : Fin 2} {x : OmegaReferent},
    OmegaSat t (OmegaBit n a x) ↔
    ∃ (k : ℤ),
      OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) x) ∧
      ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
      k.toNat % 2 = (a : ℕ)
```
*Note*: One can read `k` as the corresponding dyadic index (typically close to `⌊2^n * OmegaApprox t⌋`). Since `OmegaApprox t ≥ 0`, `k` is a non-negative integer, so `k.toNat` preserves the value for parity testing.

**Formal scope**: A bit `a` at precision `n` is equivalent to placing the continuous value in a **dyadic window**: *true at the lower cut*, and *not true at the upper cut* (`¬ OmegaSat …`), with parity constraint. The bit is thus formalized as an **emergent property** of a continuous topology, rather than an isolated atom.
