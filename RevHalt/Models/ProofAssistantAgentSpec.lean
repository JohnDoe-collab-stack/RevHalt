import Mathlib.Data.List.Basic

/-!
# ProofAssistantAgentSpec.lean

Lean skeleton encoding the key definitions from docs/ProofAssistantAgent_Spec.md.
This file ensures documentation and Lean remain synchronized.

## Corrections Applied (v2)
- `TraceOK` uses `TraceOKList` (recursive, no omega/Fin)
- Bridge assumptions section added (S.K = K, S.Machine = aMachine)
-/

namespace RevHalt.ProofAssistantAgent

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Core Types (Option B)
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Context Goal : Type)

structure ProofState where
  ctx : Context
  goals : List Goal
  depth : Nat

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Measure and Descent
-- ═══════════════════════════════════════════════════════════════════════════════

def μ (st : ProofState Context Goal) : Nat × Nat :=
  (st.depth, st.goals.length)

def LexLt (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Success and Transitions
-- ═══════════════════════════════════════════════════════════════════════════════

def Success (st : ProofState Context Goal) : Prop :=
  st.goals = []

variable (ValidTransition : ProofState Context Goal → ProofState Context Goal → Prop)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) R1: Admissible Sequences (Lexicographic)
-- ═══════════════════════════════════════════════════════════════════════════════

def Adm (s : Nat → ProofState Context Goal) : Prop :=
  (∀ n, LexLt (μ Context Goal (s (n+1))) (μ Context Goal (s n))) ∧
  (∀ n, ValidTransition (s n) (s (n+1)))

def AdmitsConst (Adm' : (Nat → ProofState Context Goal) → Prop) : Prop :=
  ∀ st : ProofState Context Goal, Adm' (fun _ => st)

theorem Adm_not_admits_const [Inhabited (ProofState Context Goal)] :
    ¬ AdmitsConst Context Goal (Adm Context Goal ValidTransition) := by
  intro hConst
  let st : ProofState Context Goal := default
  have hAdm := hConst st
  have hlt := hAdm.1 0
  cases hlt with
  | inl h => exact Nat.lt_irrefl _ h
  | inr h => exact Nat.lt_irrefl _ h.2

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) PropT: Certificate Types
-- ═══════════════════════════════════════════════════════════════════════════════

variable (PolicyId : Type)

inductive PropT where
  | Thm (Γ : List (ProofState Context Goal)) (st : ProofState Context Goal)
  | StabChain (st0 : ProofState Context Goal) (policy : PolicyId) (s : Nat → ProofState Context Goal)
  | StabFrom (st0 : ProofState Context Goal) (policy : PolicyId)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) TraceOK (Recursive, no omega/Fin)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Single step validity: descent + valid transition -/
def StepOK (a b : ProofState Context Goal) : Prop :=
  LexLt (μ Context Goal b) (μ Context Goal a) ∧ ValidTransition a b

/-- Recursive trace validity on a list -/
def TraceOKList : List (ProofState Context Goal) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => StepOK Context Goal ValidTransition a b ∧ TraceOKList (b :: rest)

/-- Full trace validity: Γ ++ [st] must be valid -/
def TraceOK (Γ : List (ProofState Context Goal)) (st : ProofState Context Goal) : Prop :=
  TraceOKList Context Goal ValidTransition (Γ ++ [st])

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Eval and EvalOnChain
-- ═══════════════════════════════════════════════════════════════════════════════

def Eval (Γ : List (ProofState Context Goal)) (st : ProofState Context Goal) : Prop :=
  Success Context Goal st ∧ TraceOK Context Goal ValidTransition Γ st

def prefix' (s : Nat → ProofState Context Goal) (n : Nat) : List (ProofState Context Goal) :=
  List.ofFn (fun i : Fin n => s i.val)

def EvalOnChain (s : Nat → ProofState Context Goal) (n : Nat) : Prop :=
  Eval Context Goal ValidTransition (prefix' Context Goal s n) (s n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Truth
-- ═══════════════════════════════════════════════════════════════════════════════

def Truth : PropT Context Goal PolicyId → Prop
  | .Thm Γ st => Eval Context Goal ValidTransition Γ st
  | .StabChain st0 _ s =>
      (s 0 = st0) ∧ Adm Context Goal ValidTransition s ∧ (∀ n, ¬ EvalOnChain Context Goal ValidTransition s n)
  | .StabFrom st0 _ =>
      ∀ s, (s 0 = st0 ∧ Adm Context Goal ValidTransition s) → (∀ n, ¬ EvalOnChain Context Goal ValidTransition s n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 9) Implementation Obligations (Axioms)
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Code : Type)
variable (HaltCertificate StabCertificate : Code → Prop)
variable (decodeΓ : Code → List (ProofState Context Goal))
variable (decodeSt decodeSt0 : Code → ProofState Context Goal)
variable (decodePolicy : Code → PolicyId)
variable (runChain : Code → Nat → ProofState Context Goal)

/-- C-Halt: correctness of decode under halt certificate -/
axiom C_Halt : ∀ e, HaltCertificate e →
  Eval Context Goal ValidTransition (decodeΓ e) (decodeSt e)

/-- C-Stab: correctness of runChain under stabilization certificate -/
axiom C_Stab : ∀ e, StabCertificate e →
  Truth Context Goal ValidTransition PolicyId
    (PropT.StabChain (decodeSt0 e) (decodePolicy e) (runChain e))

-- ═══════════════════════════════════════════════════════════════════════════════
-- 10) Bridge Assumptions (for passerelle Arch → OraclePick)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Bridge Typing Requirements

To lift `ArchitecturalOraclePick` to `Complementarity.OraclePick`, the following must hold:

1. **Kit equality**: `S.K = K` where `K` is the kit used in the architecture
2. **Machine equality**: `∀ e, S.Machine e = aMachine e`

These conditions ensure that `Rev0_K K (aMachine e)` (from architecture) matches
`Rev0_K S.K (S.Machine e)` (required by OraclePick) without transport.

**Recommended approach**: Define `S := ⟨K, aMachine, ...⟩` directly, making equalities `rfl`.
-/

end RevHalt.ProofAssistantAgent

-- Axiom check
#print axioms RevHalt.ProofAssistantAgent.Adm_not_admits_const
