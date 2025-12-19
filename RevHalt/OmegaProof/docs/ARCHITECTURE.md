# Ω-Proof: T3 Architecture Internals

**Neural-Guided Halting** is a hybrid architecture where a neural network accelerates formal proofs without compromising soundness.

## System Diagram

```mermaid
graph TD
    T[Trace input] --> S2H[S2 Heuristic Wrapper]
    
    subgraph "Internal World (S2)"
        S2H --> |Propose| ML[Witness Model]
        ML --> |Index n| S2H
        S2H --> |Verify T(n)| S2[S2 Extended Prover]
        S2 --> |Certified?| D2{Decision?}
    end
    
    subgraph "External World (S1)"
        D2 -->|UNKNOWN| S1[S1 Oracle]
    end
    
    D2 -->|HALTS/NOHALT| RES[Result]
    S1 -->|HALTS/NOHALT| RES
```

## Component Roles

### 1. `ml_witness.py` (The Proposer)
*   **Input**: Raw bit trace ($N=10$).
*   **Output**: Softmax distribution over indices $0..N$.
*   **Role**: **Intuition**. It guesses *where* the halting event happens. It doesn't need to be 100% correct, just helpful.

### 2. `s2_extended.py` (The Verifier)
*   **Logic**:
    *   **Monotone Check**: Is $T$ already filled with 1s? (Switchpoint)
    *   **Witness Check**: Is $T[n] == 1$?
*   **Role**: **Rigor**. It only signs a certificate if the fact is mechanically verified.

### 3. `s1_oracle.py` (The Judge)
*   **Logic**: Full evaluation (potentially infinite search, simulated by perfect knowledge here).
*   **Role**: **Truth**. Used only when S2 (Logic + Intuition) fails.

## Data Flow
1.  **Trace** enters `t3_policy.py`.
2.  **S2** attempts to find a proof.
    *   First, cheap Monotone check.
    *   Then, ML queries for candidate witnesses.
3.  If **Proof Found**: Return `source="S2+ML"`.
4.  If **Proof Failed**: Forward to **S1 Oracle**. Return `source="S1"` (provenance tracked).
