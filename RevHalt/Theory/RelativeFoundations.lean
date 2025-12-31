import RevHalt.Theory.ThreeBlocksArchitecture

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

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. Evaluative Dichotomy (EM_Eval)
-- ═══════════════════════════════════════════════════════════════════════════════

variable {Sentence Model : Type}
variable (A : OracleMachine Sentence Model)

/-- The Principle of Evaluative Decidability (Operational Access) -/
def EM_Eval (Γ : List Sentence) : Prop :=
  ∀ φ : Sentence, A.Eval Γ φ ∨ ¬ A.Eval Γ φ

/-- Evaluative LPO: Can we decide "Existential Eval" on a sequence of sentences? -/
def LPO_Eval (Γ : List Sentence) : Prop :=
  ∀ s : ℕ → Sentence, (∃ n, A.Eval Γ (s n)) ∨ (∀ n, ¬ A.Eval Γ (s n))

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
