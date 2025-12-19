# Ω-Proof: Complexity Analysis

This document formalizes the **Computational Complexity** of the T3 Architecture components, clarifying why the system is "non-black-box".

## 1. The P-Time Verification (S2)

The core claim "We have the P" refers to the **verification cost** of S2 certificates.

### A. Witness Certificate
*   **Structure**: `{"logic": "Witness", "index": n}`
*   **Verification**: `T.check(n)`
*   **Complexity**: **O(1)** (Direct Access) or **O(bound)** (Linear Scan) depending on trace storage.
*   **Class**: **P** (Polynomial in trace size).

### B. Monotone Certificate
*   **Structure**: `{"logic": "Monotone", "switchpoint": sp}`
*   **Verification**: `check monotone property` + `check switchpoint`.
*   **Complexity**: **O(bound)** (Linear Scan).
*   **Class**: **P**.

**Conclusion**: S2 is a **Polynomial-Time Verifier**. It does not solve the Halting Problem; it verifies *proofs* of halting.

## 2. The Heuristic Search (S2 + ML)

The combination `S2 + ML` operates as an **NP-style system**:
*   **Prover (ML)**: Non-deterministic suggestion (simulated by Neural Net). Cost: **O(Inference)**.
*   **Verifier (S2)**: Deterministic check. Cost: **P**.

The entire `S2+ML` block is effectively finding witnesses in **P-time** (empirically), but theoretically it is bounded by the verification cost.

**Crucially**: The "Proof" is the certificate, not the ML inference.

## 3. The Oracle (S1)

*   **Logic**: `Rev0_K(K, T)`.
*   **Complexity**:
    *   **In Finite Domain**: O(Exhaustive Search) or O(Oracle Access).
    *   **In Theory**: **Uncomputable** (requires infinite time or Oracular knowledge).
*   **Role**: S1 creates the "Ground Truth" that S2 tries to approximate.

## 4. Theoretical Alignment

| Component | Logic | Complexity Class | Artifact |
|-----------|-------|------------------|----------|
| **S2 (Verifier)** | `verify_cert(T, d)` | **P** | `t3_policy.py` |
| **ML (Prover)** | `model(T)` | **Heuristic** | `witness_model.pt` |
| **S1 (Oracle)** | `Rev0_K(T)` | **Oracle** | `s1_oracle.py` |

We have "The P" because the **final decision mechanism (`verify_cert`) is strictly polynomial**. The "Magic" (ML/Oracle) is kept outside the verification loop.
