# RevHalt Walkthrough

## Project Overview

RevHalt formalizes the dynamic interaction between logical provability and computational complexity.

## Layer 1: Arithmetization (Complete)

* **EvalnGraph**: Computable graph encoding of machine traces.
* **Witness**: Witness-carrying derivations.
* **Collapse**: Arithmetization showing that `PolyPosWC` implies P=NP.

## Layer 2: Canonization (Complete)

* **Goal**: Connect dynamic stability to `PolyPosWC`.
* **Architecture (Option C)**:
    1. **PosCompleteWC**: Stability ($S^1 = \emptyset$) implies all true instances are provable.
        * Theorem: `PosCompleteWC_of_S1Rel_empty_TSP`
    2. **PolyCompressionWC**: The "Price of P" hypothesis (provable $\implies$ short proof).
    3. **Synthesis**: `PosCompleteWC` + `PolyCompressionWC` $\to$ `PolyPosWC`.
        * Lemma: `PolyPosWC_of_PosComplete_and_PolyCompression`
* **TSP Instance**: Fully instantiated for TSP in `RevHalt.Theory.Instances.TSP_Canonization`.

## Layer 3: Dynamics (Next Steps)

* Defining the trajectory $\Gamma_n$.
* Proving Stabilization ($S^1(\omega\Gamma) = \emptyset$).
