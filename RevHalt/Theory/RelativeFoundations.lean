import RevHalt.Theory.ThreeBlocksArchitecture
import RevHalt.Base.Trace

/-!
# Relative Foundations: Syntax, Semantics, and Evaluation

This file formalizes the distinction between "Logical Truth" and "Operational Evaluation"
in the RevHalt architecture. It demonstrates that the so-called "Classical Assumptions"
(EM, LPO) are relative to the *evaluator*, not necessarily the underlying logic.

## The Three Layers

1. **Syntax**: `PropT` (Propositions), `Sentence` (Machine codes).
2. **Semantics**: `Truth : PropT → Prop` (Platonic truth).
3. **Evaluation**: `Eval : Context → Sentence → Prop` (Operational access).

## The Core Results

1. `EM_Truth`: The hypothesis that semantic truth is binary (`∀ p, Truth p ∨ ¬Truth p`).
2. `EM_Eval`: The hypothesis that the evaluator is decisive (`Decidable (Eval Γ φ)`).
3. `Base_Is_Degenerate`: The proof that `RevHalt/Base` is the special case where `Truth = id`.
-/

namespace RevHalt.RelativeFoundations

variable {PropT : Type}

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. Semantic Dichotomy (EM_Truth)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Semantic Truth Predicate -/
def SemanticTruth (Truth : PropT → Prop) := Truth

/-- The Principle of Semantic Excluded Middle -/
def EM_Truth (Truth : PropT → Prop) : Prop :=
  ∀ p : PropT, Truth p ∨ ¬ Truth p

/-- Semantic Traces -/
def TraceT (PropT : Type) := ℕ → PropT

/-- Semantic Halting: "Ultimately True" -/
def HaltsT (Truth : PropT → Prop) (T : TraceT PropT) : Prop :=
  ∃ n, Truth (T n)

/-- Semantic Stabilization: "Always False" -/
def StabilizesT (Truth : PropT → Prop) (T : TraceT PropT) : Prop :=
  ∀ n, ¬ Truth (T n)

/--
  **Theorem**: The Total Dichotomy on Semantic Traces implies EM_Truth.
  (The converse is only true for constant traces or under LPO).
-/
theorem dichotomy_imp_EM_Truth (Truth : PropT → Prop) :
    (∀ T : TraceT PropT, HaltsT Truth T ∨ StabilizesT Truth T) → EM_Truth Truth := by
  intro hDichotomy p
  let constT : TraceT PropT := fun _ => p
  cases hDichotomy constT with
  | inl hH =>
    obtain ⟨_, hp⟩ := hH
    left; exact hp
  | inr hS =>
    right; exact hS 0

/-- LPO at the semantic level: total dichotomy on semantic traces -/
def LPO_Truth (Truth : PropT → Prop) : Prop :=
  ∀ T : TraceT PropT, HaltsT Truth T ∨ StabilizesT Truth T

/--
**Dependency**: LPO_Truth Truth → EM_Truth Truth (constant trace trick).

This is the semantic-level version of the "constant sequence" argument.
Note: The converse does NOT hold in general.
-/
theorem LPO_Truth_imp_EM_Truth (Truth : PropT → Prop) :
    LPO_Truth Truth → EM_Truth Truth :=
  dichotomy_imp_EM_Truth Truth

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. Evaluative Dichotomy (EM_Eval / LPO_Eval) — Isolated Variants
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
These definitions are parameterized directly by `Eval : List Sentence → Sentence → Prop`,
without importing OracleMachine. This isolates the logical dependency.
-/

section Eval

variable {Sentence : Type}

/-- Evaluative EM: the evaluator is decisive on all sentences -/
def EM_Eval (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) : Prop :=
  ∀ φ : Sentence, Eval Γ φ ∨ ¬ Eval Γ φ

/-- Evaluative LPO: total dichotomy on sequences of sentences -/
def LPO_Eval (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) : Prop :=
  ∀ s : ℕ → Sentence, (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))

/-! Generic (axiom-free) EM from decidability. -/
theorem decidable_pred_imp_em {α : Type} (P : α → Prop)
    (hDec : ∀ x, Decidable (P x)) :
    ∀ x, P x ∨ ¬ P x := by
  intro x
  cases hDec x with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

/-! Generic (axiom-free) LPO → EM on a predicate. -/
theorem LPO_pred_imp_em {α : Type} (P : α → Prop) :
    (∀ s : ℕ → α, (∃ n, P (s n)) ∨ (∀ n, ¬ P (s n))) →
    ∀ x, P x ∨ ¬ P x := by
  intro hLPO x
  have h := hLPO (fun _ => x)
  cases h with
  | inl hex =>
      left
      rcases hex with ⟨_, hx⟩
      exact hx
  | inr hall =>
      right
      exact hall 0

/-- Decidability => EM_Eval (0 axiom) -/
theorem decidable_Eval_imp_EM_Eval
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (hDec : ∀ φ : Sentence, Decidable (Eval Γ φ)) :
    EM_Eval Eval Γ := by
  intro φ
  cases hDec φ with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

/-- LPO_Eval => EM_Eval (constant sequence trick, 0 axiom) -/
theorem LPO_Eval_imp_EM_Eval
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    LPO_Eval Eval Γ → EM_Eval Eval Γ := by
  intro hLPO φ
  have h := hLPO (fun _ => φ)
  cases h with
  | inl hex => exact Or.inl (hex.elim fun _ hx => hx)
  | inr hall => exact Or.inr (hall 0)

end Eval

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. The Degenerate Base Case
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Verification**: The `Trace` in `RevHalt.Base` is exactly `TraceT Prop` with `Truth := id`.
-/
theorem Base_Is_Degenerate :
    RevHalt.Trace = TraceT Prop := rfl

/--
  **Verification**: `Halts` in Base is `HaltsT id`.
-/
theorem Halts_Is_Degenerate (T : RevHalt.Trace) :
    RevHalt.Halts T ↔ HaltsT id T :=
  Iff.rfl

end RevHalt.RelativeFoundations

/-
  **Conclusion**:
  When we proved `dichotomy_iff_em` in the Ordinal Boundary work, we effectively proved:
  `dichotomy_imp_EM_Truth id` (and the converse for constant traces).
  This confirms that the dichotomy "at stage 0" identifies the logical strength (EM).
-/

-- Axiom checks (all should be 0 axiom):
#print axioms RevHalt.RelativeFoundations.dichotomy_imp_EM_Truth
#print axioms RevHalt.RelativeFoundations.LPO_Truth_imp_EM_Truth
#print axioms RevHalt.RelativeFoundations.decidable_pred_imp_em
#print axioms RevHalt.RelativeFoundations.LPO_pred_imp_em
#print axioms RevHalt.RelativeFoundations.decidable_Eval_imp_EM_Eval
#print axioms RevHalt.RelativeFoundations.LPO_Eval_imp_EM_Eval
#print axioms RevHalt.RelativeFoundations.Base_Is_Degenerate
#print axioms RevHalt.RelativeFoundations.Halts_Is_Degenerate
