# RevHalt: LLM/Transformer Integration Specification (Lean‑Aligned)

## Status
This document is the **reference specification** for integrating a Large Language Model (Transformer) with the RevHalt architecture.  
Every interface, invariant, and constraint below is aligned with the provided Lean sources:

- `ThreeBlocksArchitecture.lean`
- `RelativeFoundations.lean`
- `RelativeR1.lean`
- `Impossibility.lean`
- `Complementarity.lean`
- `QuantifierSwap.lean`
- `Dynamics.lean`
- `Stabilization.lean`
- `Categorical.lean`
- `Canonicity.lean` (for canonicity/monotonicity assumptions used by stabilization lemmas)

No claim here exceeds what these files define or prove.

---

## 0. Core Types and Notation

### 0.1 Types
| Symbol | Type | Meaning |
|---|---|---|
| `Sentence` | Type | Syntactic universe of statements |
| `Model` | Type | Semantic universe (models for `Sat`) |
| `Code` | Type | Executable code (input to the a‑machine) |
| `PropT` | Type | Internal proposition type (corpus elements) |
| `Trace` | Type | Boolean trace (`ℕ → Prop`) |
| `Γ` | `List Sentence` | Effective context (“Gamma”) |
| `s` | `ℕ → Sentence` | Sequence of sentences |
| `S` | `Set PropT` | Corpus/state set of internal propositions |

### 0.2 Separation Discipline (Non‑Negotiable)
RevHalt requires strict separation of:
1) **Decidability** (constructive, pointwise) — a property of a specific statement/property.
2) **Evaluation** (`Eval`, R3 access) — a parameterized access mechanism, not a logical axiom.
3) **Logical principles** (EM/LPO) — treated as *properties* (global or local), never silently assumed.

---

## 1. The Three‑Blocks Architecture (OracleMachine)

### 1.1 a‑machine (Mechanical Substrate)
**Lean interface:**
- `aMachine := Machine`
- `Converges (e : Code) : Prop := ∃ x, x ∈ e.eval 0`
- `Halts (aMachine e) ↔ Converges e`

**Invariant A1 (Mechanical Purity):**  
The a‑machine is purely mechanical: it supplies no oracle power and introduces no semantics.

**Source:** `ThreeBlocksArchitecture.lean`.

---

### 1.2 c‑machine (Compilation / Choice)
**Lean interface:**
- `compile : List Sentence → Sentence → Code`

**Invariant C1 (Syntactic→Mechanical):**  
`compile` maps a syntactic pair `(Γ, φ)` to executable `Code`.

**Integration constraint C2 (Transformer placement):**  
The Transformer may be used to *implement* or *assist* `compile` (e.g., to propose `φ` or compilation parameters), but Transformer outputs have **no truth/decision status**.

**Source:** `ThreeBlocksArchitecture.lean`.

---

### 1.3 o‑machine (Oracle Bridge)
**Lean interface:**
- `Sat : Model → Sentence → Prop`
- `SemConsequences Sat : Set Sentence → Sentence → Prop`
- `OracleBridge Sat compile := ∀ Γ φ, SemConsequences Sat (Γset Γ) φ ↔ Converges (compile Γ φ)`

**Invariant O1 (Unique Non‑Mechanical Link):**  
`OracleBridge` is the only declared connection between semantics (`SemConsequences`) and mechanical behavior (`Converges`).

**Source:** `ThreeBlocksArchitecture.lean`.

---

### 1.4 Eval (R3; Derived, Not an Axiom)
**Lean definition:**
- `Eval Γ φ := Converges (compile Γ φ)`

**Invariant E1 (Access, Not Logic):**  
`Eval` is an access mechanism (R3). EM/LPO properties about `Eval` are studied as *properties*, never assumed.

**Source:** `ThreeBlocksArchitecture.lean`.

---

## 2. Decidability vs Evaluation vs EM/LPO

### 2.1 Decidability (Constructive, Pointwise)
Only the following *local* forms appear in the formal development:
- `Decidable (Eval Γ φ)` (strong form), or at minimum
- a witness `Eval Γ φ ∨ ¬Eval Γ φ` (weak form)

No global decidability is assumed unless explicitly stated as a hypothesis.

**Source:** `ThreeBlocksArchitecture.lean`.

---

### 2.2 EM (Excluded Middle): Global vs Local‑to‑Eval
**Lean definitions (local):**
- `EM_Eval Eval Γ := ∀ φ, Eval Γ φ ∨ ¬ Eval Γ φ`

**Clarification:**  
`EM_Eval` is a property of the access mechanism `Eval` at a given `Γ`, not global EM.

**Source:** `RelativeFoundations.lean` (and also restated in `RelativeR1.lean`).

---

### 2.3 LPO at Evaluation Level
**Lean definition:**
- `LPO_Eval Eval Γ := ∀ s : ℕ → Sentence, (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬Eval Γ (s n))`

**Source:** `RelativeFoundations.lean`.

---

## 3. R1: Grammar of Admissible Sequences (Relativized LPO)

### 3.1 Definitions
**Lean definitions:**
- `Adm : (ℕ → Sentence) → Prop`
- `LPO_Eval_R1 Eval Γ Adm := ∀ s, Adm s → ((∃n, Eval Γ (s n)) ∨ (∀n, ¬Eval Γ (s n)))`
- `AdmitsConst Adm := ∀ φ, Adm (fun _ => φ)`

**Source:** `RelativeR1.lean`.

### 3.2 Collapse Condition (Precisely Scoped)
**Lean theorem:**
- `AdmitsConst Adm → (LPO_Eval_R1 Eval Γ Adm → EM_Eval Eval Γ)`

**Non‑guarantee:**  
`¬AdmitsConst Adm` blocks *this constant‑sequence route* to `EM_Eval`; it is not a blanket impossibility of every other collapse route.

**Source:** `RelativeR1.lean` (`LPO_R1_imp_EM_if_const`).

---

## 4. T2: Uniformity/Closure Barrier (Internalization Target)

### 4.1 What T2 Forbids (Formal)
`Impossibility.lean` defines `InternalHaltingPredicate` (uniform internal predicate with required total/correct/complete + semidecidability structure) and proves:

- `T2_impossibility : ¬ ∃ IH : InternalHaltingPredicate, True`

**Interpretation:**  
T2 forbids an **internal uniform** decider of halting with the specified internal proof/semidecision structure.

**Source:** `Impossibility.lean`.

---

### 4.2 Architectural Transfer (External Decidability via Eval)
`ThreeBlocksArchitecture.lean` defines:
- `CompiledWitness` and `CompileCover compile := ∀ e : Code, CompiledWitness compile e` (note: **Type**, not Prop)

and proves:
- if `CompileCover compile` and `∀ Γ φ, Decidable (Eval Γ φ)` then `∀ e, Decidable (Halts (aMachine e))`.

**Source:** `ThreeBlocksArchitecture.lean` (`CompileCover`, `decidable_halts_of_decidable_eval`).

---

### 4.3 Contradiction Requires an Internalization Principle
`ThreeBlocksArchitecture.lean` introduces an explicit assumption:
- `InternalizeDecider`
and then proves:
- `contradiction_if_internalize_external_decider`

Therefore:

**Constraint T2‑C (Non‑Overclaim Rule):**  
You must **not** claim that “CompileCover + total decidability of Eval contradicts T2” unless you also assume an internalization principle of the form `InternalizeDecider`.

**Source:** `ThreeBlocksArchitecture.lean` + `Impossibility.lean`.

---

## 5. T3: Kinetic Continuation (Instancewise Extension by Certificates)

### 5.1 OraclePick (Local Certificate Carrier; Complementarity Layer)
`Complementarity.lean` defines the two‑sided pick as:

```
structure OraclePick (S : ComplementaritySystem Code PropT)
  (encode_halt encode_not_halt : Code → PropT) (e : Code) where
  p : PropT
  cert :
    (Rev0_K S.K (S.Machine e) ∧ p = encode_halt e) ∨
    (KitStabilizes S.K (S.Machine e) ∧ p = encode_not_halt e)
```

**Key constraint:**  
`OraclePick` does not compute a branch; it *carries* the branch in the certificate.

**Note (specialization):**  
In the OracleMachine specialization, the mechanical machine is `aMachine`; in the complementarity layer one typically sets `S.Machine = aMachine`.

**Source:** `Complementarity.lean` (`OraclePick`).

---

### 5.2 Sound States and Step (Dynamics Layer)
`Dynamics.lean` defines:

- `Sound Truth S := ∀ p, p ∈ S → Truth p`
- `structure State (PropT) (Truth) where S : Set PropT; sound : Sound Truth S`
- `truth_of_pick` extracts `Truth pick.p` from `pick.cert`
- `step` extends a `State` by `S := S ∪ {pick.p}` while preserving soundness

**Source:** `Dynamics.lean`.

---

### 5.3 Chain, Limit, Fairness, Schedule Invariance
`Dynamics.lean` defines:

- `schedule : ℕ → Code`
- `Fair schedule := ∀ e, ∃ n, schedule n = e`
- `AllOraclePicks D pickOf := { p | ∃ e, p = (pickOf e).p }`
- `lim Chain := ⋃ n, (Chain n).S`

and proves (under fairness):

- `lim Chain = S0.S ∪ AllOraclePicks D pickOf`

**Consequence:**  
The ω‑limit state (“omegaState”) is independent of the order of any fair schedule.

**Source:** `Dynamics.lean` (`lim_schedule_free`, `omegaState`).

---

## 6. Rigidification of the Negative (Kernel / up)

### 6.1 Trace Level (a‑machine)
- `Stabilizes T := ∀ n, ¬ T n`
- `up : Trace → Trace`
- `up_eq_bot_iff : up T = ⊥ ↔ ∀ n, ¬ T n`
- `KitStabilizes K T := ¬ Rev0_K K T`
- under `DetectsMonotone K`, `KitStabilizes K T ↔ Stabilizes T`, hence `KitStabilizes K T ↔ up T = ⊥`

**Source:** `Categorical.lean` + `Stabilization.lean`.

---

### 6.2 Eval Level (R3)
`RelativeFoundations.lean` defines:

- `upE Eval Γ s n := ∃ k, k ≤ n ∧ Eval Γ (s k)`
- `botE := fun _ => False`
- `StabilizesE Eval Γ s := ∀ n, ¬ Eval Γ (s n)`
- `upE_eq_bot_iff : upE Eval Γ s = botE ↔ StabilizesE Eval Γ s`

**Meaning:**  
A Π₁ negative (“no success ever”) is represented as a **kernel/nullity condition** (`upE = botE`), not merely “absence of proof”.

**Source:** `RelativeFoundations.lean`.

---

## 7. Transformer Integration Protocol (Strict)

### 7.1 Roles (Hard Separation)

#### Generator (Transformer)
Produces only syntax:
- `propose_phi : List Sentence → Sentence`
- optionally `propose_seq : List Sentence → (ℕ → Sentence)`

**Forbidden:** treating `propose_*` outputs as truth, decision, or certificate.

#### Formation Gate (R1)
- `Adm : (ℕ → Sentence) → Prop`

**Constraint R1‑G:**  
Whenever you use LPO‑style reasoning or ω‑search properties, sequences must satisfy `Adm`.

#### Eval (R3; derived)
- `Eval Γ φ := Converges (compile Γ φ)`

#### Local decidability witness (optional, local only)
- `witness(Γ, φ) : Eval Γ φ ∨ ¬Eval Γ φ` when available (or stronger `Decidable (Eval Γ φ)`)

No global `EM_Eval` or global `Decidable (Eval Γ φ)` is assumed by default.

---

### 7.2 Minimal Integration Interfaces (API)
```text
Generator (Transformer):
  propose_phi : List Sentence -> Sentence
  propose_seq : List Sentence -> (ℕ -> Sentence)      (optional)

R1:
  Adm : (ℕ -> Sentence) -> Prop

c-machine:
  compile : List Sentence -> Sentence -> Code

a-machine:
  Converges : Code -> Prop

R3 (derived):
  Eval(Γ, φ) := Converges(compile(Γ, φ))

Optional local witness:
  witness(Γ, φ) : Eval(Γ, φ) ∨ ¬Eval(Γ, φ)            (when available)
```

---

### 7.3 Kinetic Workflow (T3-Compatible)

At step `t`:
1) **Generate:** `φ_t := propose_phi(Γ_t)`
2) **Compile:** `e_t := compile(Γ_t, φ_t)`
3) **Evaluate (R3):** `Eval(Γ_t, φ_t)` is `Converges(e_t)`
4) **(Optional) obtain a local witness:** `h_t : Eval(Γ_t, φ_t) ∨ ¬Eval(Γ_t, φ_t)`

5) **Certificate carriers (two distinct layers):**
   - **Architecture layer (ThreeBlocksArchitecture):** from `h_t` one may build an
     `ArchitecturalOraclePick A K Γ_t φ_t` whose `cert : HaltCertificate ∨ StabCertificate`.
   - **Complementarity layer (Complementarity/Dynamics):** the Dynamics step consumes an
     `OraclePick S encode_halt encode_not_halt e_t`, i.e., a commitment `p : PropT` plus
     a certificate tying `p` to `encode_halt/encode_not_halt`.

   **Integration requirement:** if you start from an `ArchitecturalOraclePick`, you must
   provide an explicit *encoding/commitment layer* (choice of `PropT`, `encode_*`, and how
   the architectural certificate induces `p = encode_halt e` or `p = encode_not_halt e`)
   before applying the `Dynamics.step` interface.

6) **Extend state (Dynamics):** `st_{t+1} := step(st_t, pick_t)` (where `pick_t` is a Complementarity `OraclePick`)
7) **Iterate under a schedule**; compute ω‑limit via `lim Chain`.

**Soundness:** preserved by construction (`truth_of_pick` and `step`).

**Source:** `ThreeBlocksArchitecture.lean` + `Complementarity.lean` + `Dynamics.lean`.

---

## 8. Safety / Non‑Overclaim Matrix (Exact)

| Statement | Allowed? | Formal condition |
|---|---:|---|
| “Transformer decides truth” | No | Not represented in Lean |
| “Eval is an axiom” | No | `Eval := Converges ∘ compile` |
| “EM_Eval holds” | Only as hypothesis/property | `EM_Eval Eval Γ` is definable, not assumed |
| “LPO_R1 ⇒ EM_Eval” | Only conditionally | Requires `AdmitsConst Adm` |
| “CompileCover + total decidability of Eval ⇒ halting decidable” | Yes | Proven in `ThreeBlocksArchitecture.lean` |
| “That contradicts T2” | Only conditionally | Requires `InternalizeDecider` |
| “T3 yields sound extensions” | Yes | By `OraclePick` + `step` + `truth_of_pick` |
| “Negative becomes kernel” | Yes | `up_eq_bot_iff`, `upE_eq_bot_iff` |

---

# Appendix A — One‑Page API Contract (Implementation Checklist)

## A1. Components
1) **Transformer Generator**
- `propose_phi(Γ) -> φ`
- optional `propose_seq(Γ) -> s`

2) **R1 Gate**
- `Adm(s) : Prop` (or implementable boolean predicate)
- Enforce: only pass `s` forward if `Adm(s)`.

3) **Compiler**
- `compile(Γ, φ) -> e : Code`

4) **Mechanical Runner**
- `Converges(e) : Prop` (or an operational proxy returning a witness when possible)

5) **Access (R3)**
- `Eval(Γ, φ) := Converges(compile(Γ, φ))`

6) **Optional Local Witness Provider**
- provide `Eval(Γ, φ) ∨ ¬Eval(Γ, φ)` when possible (not globally required)

7) **Certificate carriers**
- Architecture: `ArchitecturalOraclePick` (certifies `HaltCertificate ∨ StabCertificate`)
- Complementarity: `OraclePick` (commits `p : PropT` with equality-to-encoding certificate)

8) **Dynamics**
- `State(S, sound)`
- `step(st, pick) -> st'` (consumes Complementarity `OraclePick`)
- `Chain(schedule, pickOf)`
- `lim(Chain)`; fairness yields schedule‑invariance.

## A2. Invariants (Must Hold)
- **Soundness:** only items added via Complementarity `OraclePick.cert` are stored in `State.S`.
- **Separation:** Generator ≠ Eval ≠ EM.
- **R1‑relativization:** LPO‑style properties only quantify over `Adm` sequences.
- **T2 compliance:** never assert an internal uniform halting predicate; track internalization assumptions explicitly.

---
