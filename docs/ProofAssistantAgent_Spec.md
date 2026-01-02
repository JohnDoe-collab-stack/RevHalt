# RevHalt: Proof Assistant Agent Specification (Reinforced Version)

## Status
This is the **complete specification** for integrating a Proof Assistant Agent (Lean/Coq) with the RevHalt architecture, using **Option B (ProofState)** and **lexicographic descent** for R1.

---

## 1. Types (Option B)

```lean
constant Context : Type
constant Goal : Type

structure ProofState where
  ctx : Context
  goals : List Goal
  depth : Nat
```

---

## 2. Eval (R3): Success = Goals Empty + Trace Valid

### 2.1 Success
```lean
def Success (st : ProofState) : Prop := st.goals = []
```

### 2.2 Lexicographic Measure
```lean
def μ (st : ProofState) : Nat × Nat := (st.depth, st.goals.length)

def LexLt (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)
```

### 2.3 Valid Transition (Kernel-Checked)
```lean
constant ValidTransition : ProofState → ProofState → Prop
```

### 2.4 Trace Validity
```lean
def TraceOK (Γ : List ProofState) (st : ProofState) : Prop :=
  let tr := Γ ++ [st]
  ∀ i, i + 1 < tr.length →
    let a := tr.get ⟨i, by omega⟩
    let b := tr.get ⟨i+1, by omega⟩
    LexLt (μ b) (μ a) ∧ ValidTransition a b
```

### 2.5 Eval Definition
```lean
def Eval (Γ : List ProofState) (st : ProofState) : Prop :=
  Success st ∧ TraceOK Γ st
```

---

## 3. R1: Admissible Sequences (Lexicographic)

### 3.1 Adm Definition
```lean
def Adm (s : Nat → ProofState) : Prop :=
  (∀ n, LexLt (μ (s (n+1))) (μ (s n))) ∧
  (∀ n, ValidTransition (s n) (s (n+1)))
```

### 3.2 No Constants (Structural)
```lean
def AdmitsConst (Adm : (Nat → ProofState) → Prop) : Prop :=
  ∀ st, Adm (fun _ => st)

theorem Adm_not_admits_const : ¬ AdmitsConst Adm := by
  intro hConst
  let st := default
  have hAdm := hConst st
  have hlt := hAdm.1 0
  cases hlt with
  | inl h => exact Nat.lt_irrefl _ h
  | inr h => exact Nat.lt_irrefl _ h.2
```

---

## 4. PropT: Thm | StabChain | StabFrom

### 4.1 Definition
```lean
constant PolicyId : Type

inductive PropT where
| Thm (Γ : List ProofState) (st : ProofState)
| StabChain (st0 : ProofState) (policy : PolicyId) (s : Nat → ProofState)
| StabFrom (st0 : ProofState) (policy : PolicyId)
```

### 4.2 Evaluation on Chain
```lean
def prefix (s : Nat → ProofState) (n : Nat) : List ProofState :=
  List.ofFn (fun i : Fin n => s i.1)

def EvalOnChain (s : Nat → ProofState) (n : Nat) : Prop :=
  Eval (prefix s n) (s n)
```

### 4.3 Truth
```lean
def Truth : PropT → Prop
| .Thm Γ st => Eval Γ st
| .StabChain st0 policy s =>
    (s 0 = st0) ∧ Adm s ∧ (∀ n, ¬ EvalOnChain s n)  -- Π₁
| .StabFrom st0 policy =>
    ∀ s, (s 0 = st0 ∧ Adm s) → (∀ n, ¬ EvalOnChain s n)  -- Π₂
```

---

## 5. Passerelle: ArchitecturalOraclePick → OraclePick

### 5.1 Encoding Functions
```lean
constant decodeΓ : Code → List ProofState
constant decodeSt : Code → ProofState
constant decodeSt0 : Code → ProofState
constant decodePolicy : Code → PolicyId
constant runChain : Code → (Nat → ProofState)

def encode_halt (e : Code) : PropT :=
  PropT.Thm (decodeΓ e) (decodeSt e)

def encode_not_halt (e : Code) : PropT :=
  PropT.StabChain (decodeSt0 e) (decodePolicy e) (runChain e)
```

### 5.2 Lift Construction
```lean
def lift_arch_to_oraclepick
  (A : OracleMachine Sentence Model)
  (K : RHKit)
  (S : ComplementaritySystem Code PropT)
  (Γ : List Sentence) (φ : Sentence)
  (pick : ArchitecturalOraclePick A K Γ φ) :
  OraclePick S encode_halt encode_not_halt pick.code := by
  cases pick.cert with
  | inl hH => exact ⟨encode_halt pick.code, Or.inl ⟨hH, rfl⟩⟩
  | inr hS => exact ⟨encode_not_halt pick.code, Or.inr ⟨hS, rfl⟩⟩
```

---

## 6. Summary

| Component | Definition |
|---|---|
| `Sentence` | `ProofState` |
| `Eval` | `Success st ∧ TraceOK Γ st` |
| `Adm` | Lexicographic descent + ValidTransition |
| `¬AdmitsConst` | Structural (irref of LexLt) |
| `PropT` | `Thm` (Σ₁) / `StabChain` (Π₁) / `StabFrom` (Π₂) |
| Passerelle | `ArchitecturalOraclePick → OraclePick` via encode |

---

## 7. Solved Problems

1. **Hallucination**: Proofs enter State only via `Eval` + certificate
2. **Refusal**: "NO" = `StabChain`/`StabFrom` (structural kernel)
3. **Power Control**: R1 lexicographic + `¬AdmitsConst`
4. **No Omniscience**: T2 barrier applies
5. **Traceability**: T3 dynamics with `step` + `lim`

---

## 8. Implementation Obligations (decode*/runChain)

### 8.1 Halt Path (C-Halt)
For every `e : Code`, if the architecture provides a halt certificate for `e`, then:
- `Success (decodeSt e)` (goals empty)
- `TraceOK (decodeΓ e) (decodeSt e)` (valid trace with descent)
- Hence `Eval (decodeΓ e) (decodeSt e)`

### 8.2 Stabilization Path (C-Stab)
For every `e : Code`, if the architecture provides a stabilization certificate for `e`, then:
- `runChain e 0 = decodeSt0 e` (correct start)
- `Adm (runChain e)` (admissible chain)
- `∀n, ¬EvalOnChain (runChain e) n` (no success along chain)
- Hence `Truth (StabChain (decodeSt0 e) (decodePolicy e) (runChain e))`

### 8.3 Reproducibility (Recommended)
`runChain` should be deterministic/replayable with respect to the exact policy/config embedded by `compile`, so that the certificate refers to the same executed trajectory that `runChain` denotes.

### 8.4 Pi-2 Global Negatives
`StabFrom` is NOT obtained from `runChain`. It requires a separate global argument over all admissible chains (meta-proof, completeness, or exhaustion).

---

## 9. Journal-Based Implementation (Recommended Pattern)

For `compile = search + kernel-check + journaling`:

```lean
structure JournaledRun where
  trace : List ProofState
  policy : PolicyId
  outcome : Outcome  -- Success st | Exhausted

def decodeΓ (e : Code) : List ProofState := (journal e).trace.dropLast
def decodeSt (e : Code) : ProofState := (journal e).trace.getLast!
def decodeSt0 (e : Code) : ProofState := (journal e).trace.head!
def decodePolicy (e : Code) : PolicyId := (journal e).policy
def runChain (e : Code) : Nat → ProofState := fun n => (journal e).trace.getD n default
```

This makes `decode*` trivial projections, minimizing bug surface.

---

## Appendix A: Traceability to Lean

| Spec Concept | Lean Definition | Source File |
|---|---|---|
| `Eval := Converges ∘ compile` | `OracleMachine.Eval` | `ThreeBlocksArchitecture.lean` |
| `EM_Eval`, `LPO_Eval` | `EM_Eval`, `LPO_Eval` | `RelativeFoundations.lean` |
| `upE_eq_bot_iff` | `upE_eq_bot_iff` | `RelativeFoundations.lean` |
| `Adm`, `AdmitsConst` | `Adm`, `AdmitsConst` | `RelativeR1.lean` |
| `LPO_R1_imp_EM_if_const` | `LPO_R1_imp_EM_if_const` | `RelativeR1.lean` |
| `InternalHaltingPredicate` | `InternalHaltingPredicate` | `Impossibility.lean` |
| `T2_impossibility` | `T2_impossibility` | `Impossibility.lean` |
| `OraclePick` | `OraclePick` | `Complementarity.lean` |
| `State`, `step`, `lim` | `State`, `step`, `lim` | `Dynamics.lean` |
| `omegaState`, `lim_schedule_free` | `omegaState`, `lim_schedule_free` | `Dynamics.lean` |
| `up_eq_bot_iff` | `up_eq_bot_iff` | `Categorical.lean` |
| `KitStabilizes ↔ Stabilizes` | `T1_stabilization` | `Stabilization.lean` |
| `DetectsMonotone` | `DetectsMonotone` | `Canonicity.lean` |

---

## Appendix B: Glossary (Pi-1 / Pi-2)

| Term | Level | Definition |
|---|---|---|
| `StabChain` | Π₁ | Stabilization along ONE fixed chain: `∀n, ¬EvalOnChain s n` |
| `StabFrom` | Π₂ | Universal over ALL admissible chains: `∀s, Adm s → ∀n ¬EvalOnChain s n` |
| Refutation `¬φ` | N/A | NOT identified with `Stab*` unless a specific certificate proves it |
| Kernel (`up = ⊥`) | Π₁ | Structural nullity, not logical negation |

**Rule**: `StabChain` is what `runChain` can produce. `StabFrom` requires meta-proof.

---

## Appendix C: Conformance Test Outline

1. **Success Test**: Provide a `JournaledRun` with `outcome = Success st` where:
   - `decodeSt e` has `goals = []`
   - `TraceOK (decodeΓ e) (decodeSt e)` holds
   - Verify `Eval (decodeΓ e) (decodeSt e)`

2. **Stabilization Test**: Provide a `JournaledRun` with `outcome = Exhausted` where:
   - `runChain e 0 = decodeSt0 e`
   - `Adm (runChain e)`
   - `∀n, ¬EvalOnChain (runChain e) n`

3. **Anti-Constant Test**: Verify `Adm_not_admits_const` is provable for the effective `Adm`.
