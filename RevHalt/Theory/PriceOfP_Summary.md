# Price of P: Synthesis and Architecture

## Core Philosophy

**"Price of P"** is not an algorithmic search procedure itself, but a **structural data object** (`PolyPosWC`).
**"Collapse"** is the **constructive derivation** of a decision procedure (`Find`) from this object.

The central equation is:
> **Price of P = Data (PolyPosWC)**
> **Collapse = Construction (Find from Data)**

## Key Formalisms

### 1. The Data Object: `PolyPosWC`

Defined in `RevHalt.Theory.TheoryDynamics_ComplexityBounds`.
It asserts the existence of **polynomially bounded witness-carrying derivations**.

- **Witness-Carrying**: Proofs that carry a witness (e.g., a TSP tour).
- **Polynomially Bounded**: The code size of the derivation is bounded by $B(\text{size}(input))$, where $B$ is a polynomial.

### 2. The Construction: `Collapse_TSP_Axiom_of_Poly`

Defined in `RevHalt.Theory.Instances.TSP`.
This function constructs a `Collapse_TSP_Axiom` (which packages a computable `Find` function) solely from a `PolyPosWC` instance.

- **Find_poly**: Explicitly enumerates derivations up to the bound $B$.
- **Correctness/Completeness**: Guaranteed by the `PolyPosWC` properties.

## Trajectory Connection

We have formally connected this static architecture to the dynamic RevHalt trajectory ($\Gamma_0 \to \dots \to \omega\Gamma$).

### Lemma A: Monotonicity (Transport)

**`RevHalt.Complexity.PolyPosWC_monotone`**
If a polynomial bound holds for a theory state $\Gamma$, it holds for any extension $\Gamma' \supseteq \Gamma$.

- *Significance*: Bounds established at any finite stage are preserved at the limit.

### Lemma B: Limit Derivation

**`RevHalt.TSP.Collapse_of_Trajectory_Poly`**
If the trajectory limit $\omega\Gamma$ possesses the `PolyPosWC` structure, then `Collapse_TSP_Axiom` is derivable.

- *Significance*: The limit object is sufficient to grounding P=NP.

### Lemma C: Finite Stage Propagation

**`RevHalt.TSP.Collapse_of_TrajectoryStage_Poly`**
If any finite stage $\Gamma_n$ of the trajectory produces `PolyPosWC`, then:

1. The bound lifts to $\omega\Gamma$ (via Monotonicity).
2. The limit derives Collapse (via Limit Derivation).
3. **Conclusion**: P=NP is constructively established for TSP.

## Summary Status

- **Constructive**: All definitions are `def` or constructive proofs. No `noncomputable` or classical choice used for the search procedure.
- **Input/Output**: `PolyPosWC` is the *output* of the dynamic analysis (Layer 2), and the *input* to the complexity collapse (Layer 1).
