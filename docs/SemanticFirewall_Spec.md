# Semantic Firewall: Generalizing RevHalt to Secure Transactions

**"RevHalt is not about halting. It is about the secure composition of certified steps."**

This document instantiates the RevHalt architecture for a **Secure Transaction Agent**, demonstrating that the same framework used for formal verification applies directly to **Cyber-Physical Safety** and **Smart Contract Security**.

---

## 1. The Core Concept

Current LLM Agents in finance/crypto are dangerous because they are probabilistic generators given write access to deterministic ledgers.
**The RevHalt Solution**: The "Semantic Firewall" architecture where the model is *never* an authority.

*   **Proposer (C-Machine)**: The LLM generates candidate transactions/strategies.
*   **Verifier (O-Machine)**: A deterministic sandbox (EVM, Sim) checks validity.
*   **Gate (R1)**: A policy filter enforces invariants (solvency, max gas, anti-replay).
*   **Certifier (PropT)**: Only states with a cryptographic/proven certificate enter the permanent record.

---

## 2. Architecture Mapping

| Abstract RevHalt Component | Secure Transaction Instantiation |
| :--- | :--- |
| **Sentence ($S$)** | `TxFrame` (Ledger State + Tx + Gas + Status) |
| **C-Machine (LLM)** | The "Wallet Agent" (proposing transfers, interactions) |
| **Gate (R1)** | `PolicyStepOK` ∧ `DescExec` (Gas ↓) |
| **O-Machine (Eval)** | `Success` (Committed status) ∧ `TraceOK` (EVM Validity) |
| **Truth** | Reachability: "This state is reachable by a valid execution trace" |
| **PropT (Certificates)** | `Committed` (Success), `DeadEnd` (Rejection), `BudgetExhausted` |
| **T3 (Dynamic Extension)** | The Blockchain itself: an ever-growing set of certified states `S1` |

### The "R1_exec" vs "R1_meta" Distinction
To avoid vacuity (proving termination by simply crashing), we separate strictly:

1.  **R1_exec (Runtime)**: Strictly well-founded (Gas decreases).
    *   Ensures every transaction logic *halts* (runs out of gas or commits).
    *   Negatives are **Operational**: "DeadEnd" (policy violation) or "BudgetExhausted".
2. **R1_meta (Theoretical)**: Not used at runtime.
    *   Handles infinite chains (e.g., protocol liveness proofs).
    *   Stabilization certificates (`StabChain`) belong here and are **blocked** by the firewall at runtime.

---

## 3. The Certificate Typology (Operational)

The agent does not "believe" things; it holds **Certificates**.

1.  **$\Sigma_1$ / Committed**:
    *   "I possess a trace $\Gamma$ where `EVM(Γ) = Valid` AND `Policy(Γ) = OK` AND `EndState.status = Committed`."
    *   This is a proof of success.

2.  **Operational Negative / DeadEnd**:
    *   "I possess a trace $\Gamma$ ending in `st`, where `Gate(st, next) = False` for all `next` proposed."
    *   Includes an audit trail (why policy rejected it).
    *   This is a **constructive failure**, not a lack of knowledge.

3.  **BudgetExhausted**:
    *   "I ran validly for $N$ steps but GAS hit 0 before Commit."

---

## 4. Why this is stronger than "Guardrails"

Standard "Guardrails" are often regexes or auxiliary models (probabilistic).
The **Semantic Firewall** is **Structural**:
*   The "State" object `TxFrame` acts as a monad that *cannot be constructed* without a certificate.
*   The Agent cannot "hallucinate" a transaction into the ledger; the `Eval` function is part of the state definition.
*   **If it's in the state, it's verified.**

## 5. Implementation Status

*   **Spec**: `RevHalt/Models/SecureTransactionAgentSpec.lean` (Done)
*   **Status**: Ready for Simulator Implementation.
