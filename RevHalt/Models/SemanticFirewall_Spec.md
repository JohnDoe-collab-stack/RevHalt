# RevHalt Semantic Firewall
## Secure Transaction Agent Instantiation (Reference Specification)

### Purpose
Demonstrate that RevHalt is a **general control architecture** for untrusted generators (including LLMs): the model proposes, a trusted mechanism verifies, and only verified artifacts are admitted into state.

This instantiation targets **secure transactions / smart contracts**:
- the generator proposes transaction steps (or full transactions),
- a policy gate enforces hard constraints (anti-replay, allowlists, gas bounds, solvency),
- a verifier (EVM sandbox / formal semantics / kernel) validates execution,
- certificates are stored with a soundness invariant.

This is a *spec-first* deliverable aligned with the RevHalt Lean separation discipline:
**Decidability** (constructive, local), **Evaluation** (R3 mechanism), and **Logical principles** (EM/LPO) remain distinct.

---

## 1. Mapping to the Three-Blocks Architecture

| RevHalt block | In this instantiation | Trust boundary |
|---|---|---|
| a-machine | deterministic execution substrate (EVM interpreter / sandbox runner) | trusted for step semantics, no oracle power |
| c-machine | transaction proposer (LLM, wallet agent, planner) | untrusted |
| o-machine | semantic verifier (kernel / formal semantics witness) | trusted |
| R1 | policy and admissibility gate | trusted |
| Eval (R3) | “Committed + TraceOK” (or “Outcome + TraceOK”, depending on goal) | trusted |

Key point: **the agent is not trusted to be correct**; correctness is carried by certificates.

---

## 2. Domain Types

A minimal type layer (extensible):
- `Address`, `Key`, `Bytes` (payload)
- `Tx`: {from, to, value, nonce, gasLimit, data}
- `TxState`: {balances, nonces, storage}
- `TxFrame`: {state, tx, gasLeft, pc, outcome}

`TxFrame` is the “Option B” analogue of `ProofState`: it is the unit of trace.

---

## 3. R1 Gate (Policy + Admissibility)

### 3.1 Policy
Policy is explicit data, not a prompt:
- `allow : Address -> Prop`
- `maxGas : Nat`
- `maxValue : Nat`
- `antiReplay : Bool` (nonce discipline)

### 3.2 Step-level constraints (Gate)
A step `a -> b` is admissible iff:
1. **Kernel/Semantic step**: `KernelStep π a b` (EVM semantics witness)
2. **Policy step OK**: `PolicyStepOK π a b` (solvency/allowlist/nonce/gas)
3. Optionally a **resource descent** for the execution layer: `gasLeft` strictly decreases (ensures finite traces)

Important nuance:
- If strict well-founded descent is enforced at execution level, then “infinite admissible chains” are ruled out by construction.
- Therefore the **operational negative certificate** is *not* Π₁-over-ℕ stabilization; it is **DeadEnd** (or budget exhaustion).
- Π₁/Π₂ stabilization remains meaningful only in a **meta layer** with a different grammar (e.g., non-strict or non-well-founded `Adm∞`).

---

## 4. Eval (R3): What is being verified

For a *commit-oriented* firewall, define:
- `Committed(fr)` as “final outcome is committed”,
- `TraceOK(tr)` as “every adjacent step is kernel-valid and policy-valid”.

Then:
- `Eval Γ fr := Committed(fr) ∧ TraceOK(Γ ++ [fr])`

Alternative (often useful): `Eval` validates *either* committed *or* reverted outcomes, and certificates distinguish them.

---

## 5. Certificates (PropT)

Execution-layer certificates are those that can be produced and checked from concrete runs:
- `Committed(Γ, fr)` — Σ₁ witness (trace + final frame)
- `DeadEnd(Γ, current, rejected, audit)` — operational blocking with tamper-evident audit
- `BudgetExhausted(Γ, steps, reason)` — semantic “not resolved within budget”

Meta-layer certificates (never emitted by execution exploration when using strict descent):
- `StabChain` (Π₁) — stabilization along an infinite admissible chain
- `StabFrom` (Π₂) — stabilization for all admissible chains

Rule: **meta-only certificates must not be insertable into the execution state**.

---

## 6. Soundness Invariant

A system state is a set of certificates `S` with:
- `Sound(S) := ∀ p ∈ S, Truth(p)`

`Truth` is a single-point definition; execution-layer certificates must have substantive truth checks:
- committed: recompute `Eval(prefix, final)`
- dead-end: recompute gate checks and verify stored audit fields match
- budget exhausted: recompute “no success on any prefix”

---

## 7. Deliverables

### Lean (spec)
- `SecureTransactionAgentSpec.lean`
  - types (`Tx`, `TxState`, `TxFrame`, `Policy`)
  - `TraceOK`, `Eval`
  - `Adm_exec`, `¬AdmitsConst` (if strict descent)
  - `PropT` and `Truth`
  - implementation obligations (`C_Commit`, `C_DeadEnd`, `C_Budget`) as axioms/contracts

### Documentation (spec)
- this document (mapping + invariants + what is verified)

### Optional (implementation)
- a sandboxed EVM runner producing tamper-evident journals
- a verifier binding `KernelStep` to actual semantics (e.g., Foundry/REVM, K-framework, or Lean semantics)

---

## 8. Verification Plan (what to test)

1. **Commit path (Σ₁):**
   - generator proposes a candidate step sequence
   - verifier validates every step
   - final outcome committed
   - certificate truth checks recompute all predicates

2. **DeadEnd path (operational negative):**
   - generator proposes a step rejected by gate
   - audit fields stored
   - truth checks recompute and match stored values (tamper-evident)

3. **Meta injection protection:**
   - attempt to insert `StabChain/StabFrom` into execution state must fail closed

---

## 9. Notes on “realism”

This instantiation becomes “real” when `KernelStep` is bound to a trusted verifier:
- EVM small-step semantics with replayable witnesses, or
- an external verifier with a signed journal, or
- a mechanized semantics (Lean/K) producing proof objects.

The LLM remains a proposer. The firewall’s guarantees come from the verifier and certificate discipline.
