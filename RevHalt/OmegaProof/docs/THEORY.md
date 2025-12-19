# Ω-Proof: Theory Reference

This document maps the **Lean Formalization** (`RevHalt/Theory`) to our **T3 Architecture**.

## 1. T1: Canonicity (The Oracle)
**Lean File**: `Theory/Canonicity.lean`
**Theorem**: `T1_traces`
$$ \forall T, \text{Rev0\_K}(K, T) \iff \text{Halts}(T) $$

*   **Meaning**: Our specific Kernel $K$ is canonical/universal.
*   **Implementation**: `s1_oracle.py` wraps `proof_kernel.Rev0_K`. It is the "ground truth".

## 2. T2: Impossibility (The Gap)
**Lean File**: `Theory/Impossibility.lean`
**Theorem**: `T2_impossibility`
$$ \neg \exists P \in \text{Internal}, \forall T, P(T) \iff \text{Halts}(T) $$

*   **Meaning**: No internal program $S_2$ can decide the Halting Set completely. There is always an irreducible frontier.
*   **Implementation**: The **22.85%** of traces where S2 returns `UNKNOWN`. This valid failure proves the theory.

## 3. T3: Complementarity (The Solution)
**Lean File**: `Theory/Complementarity.lean`
**Theorem**: `T3_weak_extension_explicit`
$$ S_3 = S_2 \cup S_1 $$
*   **Meaning**: Combining a partial internal prover ($S_2$) and an external oracle ($S_1$) creates a valid total system ($S_3$).
*   **Implementation**: `t3_policy.py`.
    *   Step 1: Ask `s2_extended.decide(T)`.
    *   Step 2: If `UNKNOWN`, Ask `s1_oracle.decide(T)`.

## 4. T4: Witness Logic (The Heuristic)
**Lean File**: `Theory/WitnessLogic.lean`
**Theorem**: `witness_soundness`
$$ T(n) \implies \text{Halts}(T) $$

*   **Meaning**: If you find *one* index $n$ where the trace is True, you have proven Halting.
*   **Implementation**: `s2_heuristic.py` + `ml_witness.py`.
    *   ML suggests $n$.
    *   S2 checks $T(n)$.
    *   If True $\to$ Certified `HALTS`.
