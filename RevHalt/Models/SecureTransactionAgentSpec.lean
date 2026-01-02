/-!
# SecureTransactionAgentSpec.lean

RevHalt instantiation: **Secure Transaction Agent / Semantic Firewall**.

Design intent
- **Generator (c-machine)**: proposes candidate transaction steps (untrusted).
- **Policy Gate (R1)**: enforces hard constraints (allowlist, gas, anti-replay, solvency).
- **Verifier (o-bridge / R3)**: validates semantic correctness (EVM/kernel semantics).
- **Certificates (PropT)**: what the system is allowed to *store* as truth.

This file is deliberately "interface-level": it provides Lean types and
predicates that mirror `ProofAssistantAgentSpec.lean`, while keeping
EVM/crypto semantics abstract (as constants/axioms).

Nothing here claims more than: *if you implement the abstract interfaces*,
then RevHalt-style soundness is a straightforward consequence of the
certificate discipline.
-/

import Mathlib.Data.List.Basic

namespace RevHalt.SecureTransactionAgent

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Domain Types
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Addresses (accounts / contracts). -/
constant Address : Type

/-- Storage keys (contract storage index). -/
constant Key : Type

/-- Opaque payload / calldata. -/
constant Bytes : Type

/-- Opaque signature type. -/
constant Signature : Type

/-- Transaction intent (what the generator proposes at the "intent" level). -/
structure Tx where
  from    : Address
  to      : Address
  value   : Nat
  nonce   : Nat
  gasLimit : Nat
  data    : Bytes
  sig     : Signature

/-- Ledger-like state. Keep it functional to avoid extra imports. -/
structure TxState where
  balance : Address → Nat
  nonce   : Address → Nat
  storage : Address → Key → Nat

/-- Execution phase; `running` supports multi-step execution traces. -/
inductive Phase where
  | running
  | committed
  | reverted

/-- A "Sentence" for this instantiation: a concrete execution frame. -/
structure TxFrame where
  pre     : TxState          -- state before applying the step
  tx      : Tx
  post    : TxState          -- state after applying the step
  gasLeft : Nat
  phase   : Phase
  -- Optional: revert reason hash, receipt hash, logs, etc. Kept abstract.

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Policy (R1 Gate)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Firewall policy parameters. -/
structure Policy where
  allow : Address → Prop      -- allowlist / permissioning
  maxGas : Nat                -- hard upper bound on gasLimit
  -- You can extend with: maxValue, maxCallDepth, forbidden selectors, etc.

/-- Anti-replay: nonce discipline (stateful). -/
constant NonceOK : Policy → TxState → Tx → Prop

/-- Solvency: sender has enough balance to cover value (and fees if modeled). -/
constant Solvent : Policy → TxState → Tx → Prop

/-- Signature validity (cryptographic check). -/
constant SigOK : Policy → Tx → Prop

/-- High-level policy compliance at a step boundary. -/
structure PolicyStepOK (π : Policy) (a b : TxFrame) : Prop where
  allow_from : π.allow a.tx.from
  allow_to   : π.allow a.tx.to
  gas_bound  : a.tx.gasLimit ≤ π.maxGas
  sig_ok     : SigOK π a.tx
  nonce_ok   : NonceOK π a.pre a.tx
  solvent_ok : Solvent π a.pre a.tx

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Verifier (o-bridge / semantic check)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
`KernelStep π a b` is the *trusted* semantic checker.

Interpretation options:
- EVM small-step relation inside a sandbox;
- EVM big-step execution producing `post`, `gasLeft`, and `phase`;
- A proof-producing verifier (e.g., Lean theorem about execution).

RevHalt only needs it as a relation whose truth is not provided by the generator.
-/
constant KernelStep : Policy → TxFrame → TxFrame → Prop

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Measure and R1 (two layers: exec vs meta)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Execution-layer measure used to ensure finiteness (e.g., gasLeft descent). -/
def μ_exec (fr : TxFrame) : Nat := fr.gasLeft

/-- Strict descent used by the execution R1. -/
def DescExec (a b : TxFrame) : Prop := μ_exec b < μ_exec a

/--
`Adm_exec π s` is the *execution* admissibility predicate.
It is typically strict (gas strictly decreases), so it implies finiteness.

This is exactly why execution-level negatives are **DeadEnd/BudgetExhausted**,
not Π₁ "for all n" stabilization.
-/
def Adm_exec (π : Policy) (s : Nat → TxFrame) : Prop :=
  (∀ n, KernelStep π (s n) (s (n+1))) ∧
  (∀ n, PolicyStepOK π (s n) (s (n+1))) ∧
  (∀ n, DescExec (s n) (s (n+1)))

/--
`Adm_meta π s` is the *meta* admissibility predicate.

It is intentionally *not* required to be well-founded. It is the layer where
Π₁/Π₂ stabilization statements live (when you truly quantify over ω-chains).

You can pick `Adm_meta` to model:
- fairness constraints,
- monotone grammars,
- orbit grammars,
- bounded nondeterminism,
without forcing finiteness.
-/
constant Adm_meta : Policy → (Nat → TxFrame) → Prop

/-- "AdmitsConst" as in `RelativeR1.lean`, specialized. -/
def AdmitsConst (Adm : (Nat → TxFrame) → Prop) : Prop :=
  ∀ fr, Adm (fun _ => fr)

/-- Execution R1 blocks constants structurally (strict descent). -/
theorem Adm_exec_not_admits_const [Inhabited TxFrame] (π : Policy) :
    ¬ AdmitsConst (fun s => Adm_exec π s) := by
  intro hConst
  let fr : TxFrame := default
  have h := hConst fr
  have hdesc := h.2.2 0
  -- DescExec fr fr is impossible.
  simpa [Adm_exec, DescExec, μ_exec] using (Nat.lt_irrefl _ hdesc)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Eval (R3): what the verifier actually certifies
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Success notion for this instantiation: committed final frame. -/
def Success (fr : TxFrame) : Prop := fr.phase = Phase.committed

/-- Revert notion: reverted final frame (still a verifiable outcome). -/
def Reverted (fr : TxFrame) : Prop := fr.phase = Phase.reverted


/-- Trace validity (TraceOK): every consecutive step is kernel-valid and policy-valid. -/
def TraceOK (π : Policy) : List TxFrame → Prop
| [] => True
| [_] => True
| a :: b :: rest =>
    (KernelStep π a b ∧ PolicyStepOK π a b) ∧ TraceOK π (b :: rest)

/--
Eval(Γ, fr) is the derived R3 access mechanism.

Here we use: **committed** ∧ **TraceOK** over the whole trace.
If you also want to certify reverts, see `EvalRevert` below.
-/
def Eval (π : Policy) (Γ : List TxFrame) (fr : TxFrame) : Prop :=
  Success fr ∧ TraceOK π (Γ ++ [fr])

/-- Optional secondary evaluator for certified reverts (Σ₁ negative-but-witnessed). -/
def EvalRevert (π : Policy) (Γ : List TxFrame) (fr : TxFrame) : Prop :=
  Reverted fr ∧ TraceOK π (Γ ++ [fr])

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Certificate Universe (PropT)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Audit payload for an operational rejection (tamper-evident fields live here). -/
structure DeadEndAudit where
  rejectedAt : Nat

/--
PropT: what may enter the RevHalt state.

- `Committed` and `RevertOK` are **Σ₁**: witnessed by a concrete trace.
- `DeadEnd` and `BudgetExhausted` are operational facts about exploration.
- `StabChain` and `StabFrom` are **meta-only**: Π₁ / Π₂ statements.
-/
inductive PropT where
  | Committed (π : Policy) (Γ : List TxFrame) (final : TxFrame)
  | RevertOK  (π : Policy) (Γ : List TxFrame) (final : TxFrame)
  | DeadEnd   (π : Policy) (Γ : List TxFrame) (current rejected : TxFrame) (audit : DeadEndAudit)
  | BudgetExhausted (π : Policy) (Γ : List TxFrame) (budget : Nat)
  | StabChain (π : Policy) (fr0 : TxFrame) (s : Nat → TxFrame)
  | StabFrom  (π : Policy) (fr0 : TxFrame)

/--
Truth predicate: semantic meaning of PropT.

This is the single point of definition for what it means for a certificate to be valid.
-/
def Truth : PropT → Prop
  | .Committed π Γ final => Eval π Γ final
  | .RevertOK π Γ final  => EvalRevert π Γ final
  | .DeadEnd π Γ current rejected _audit =>
      TraceOK π (Γ ++ [current]) ∧ ¬ (KernelStep π current rejected ∧ PolicyStepOK π current rejected)
  | .BudgetExhausted π Γ _budget =>
      TraceOK π Γ ∧ (∀ fr ∈ Γ, ¬ Success fr)  -- no committed state observed in the budgeted trace
  | .StabChain π fr0 s =>
      (s 0 = fr0) ∧ Adm_meta π s ∧ (∀ n, ¬ Success (s n))  -- Π₁ along one admissible ω-chain
  | .StabFrom π fr0 =>
      ∀ s, (s 0 = fr0 ∧ Adm_meta π s) → (∀ n, ¬ Success (s n)) -- Π₂: all ω-chains

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Bridge Obligations (decode*/runChain-style)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Executable code type (from `ThreeBlocksArchitecture.lean` in the core project). -/
constant Code : Type

/-- Decoders: interpret code into the domain-level objects used by PropT. -/
constant decodePolicy : Code → Policy
constant decodeTrace  : Code → List TxFrame
constant decodeFinal  : Code → TxFrame
constant decodeCurrent : Code → TxFrame
constant decodeRejected : Code → TxFrame
constant decodeBudget : Code → Nat

/--
`runChain` is the operational trajectory used for execution-layer certificates.
It is the journal projection in a replayable implementation.
-/
constant runChain : Code → Nat → TxFrame

/--
Execution-layer certificate carriers.

In an implementation these would be produced by the exploration loop.
They are *not* assumed to be decidable, only carried as data.
-/
constant HaltCertificate   : Code → Prop
constant RevertCertificate : Code → Prop
constant DeadEndCertificate : Code → Prop
constant BudgetCertificate : Code → Prop

/-- Encoding used by the complementarity bridge (halt vs not-halt analogues). -/
def encode_commit (e : Code) : PropT :=
  PropT.Committed (decodePolicy e) (decodeTrace e) (decodeFinal e)

/-- Encoding a witnessed revert (Σ₁ negative-but-witnessed). -/
def encode_revert (e : Code) : PropT :=
  PropT.RevertOK (decodePolicy e) (decodeTrace e) (decodeFinal e)

/-- Encoding an operational dead-end. -/
def encode_deadend (e : Code) : PropT :=
  PropT.DeadEnd (decodePolicy e) (decodeTrace e) (decodeCurrent e) (decodeRejected e) ⟨(decodeTrace e).length⟩

/-- Encoding an operational budget exhaustion. -/
def encode_budget (e : Code) : PropT :=
  PropT.BudgetExhausted (decodePolicy e) (decodeTrace e) (decodeBudget e)



-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Bridge pattern: Architectural pick → certificate pick
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Minimal execution-layer pick (domain-specialized analogue of `ArchitecturalOraclePick`). -/
structure ArchitecturalPick where
  code : Code
  cert : Truth (encode_commit code) ∨ Truth (encode_deadend code)

/-- Minimal complementarity pick (domain-specialized analogue of `OraclePick`). -/
structure Pick where
  p : PropT
  cert : Truth p

/-- Lift the architectural dichotomy (commit vs dead-end) into a `Pick`. -/
def lift_arch_to_pick (ap : ArchitecturalPick) : Pick := by
  refine ?_ 
  cases ap.cert with
  | inl hC =>
      exact ⟨encode_commit ap.code, hC⟩
  | inr hD =>
      exact ⟨encode_deadend ap.code, hD⟩

/--
Implementation obligations: if the runtime emits a certificate, it must satisfy `Truth`.

These are the direct analogue of C-Halt / C-Stab obligations in the proof assistant instantiation.
-/
axiom C_Commit : ∀ e, HaltCertificate e → Truth (encode_commit e)
axiom C_Revert : ∀ e, RevertCertificate e → Truth (encode_revert e)
axiom C_DeadEnd : ∀ e, DeadEndCertificate e → Truth (encode_deadend e)
axiom C_Budget : ∀ e, BudgetCertificate e → Truth (encode_budget e)

end RevHalt.SecureTransactionAgent
