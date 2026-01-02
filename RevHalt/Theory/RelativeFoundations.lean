import RevHalt.Base.Trace

/-!
# Relative Foundations: Syntax, Semantics, and Evaluation

This file algebraically formalizes meta-logic by treating logical principles as parametric properties of interpreters. It demonstrates three key mathematical insights:

## 1. Logic as a Parameter (Interpreter Property)
Instead of fixing "the" logic, we introduce **power predicates**:
* **Semantic**: `EM_Truth Truth := ∀ p, Truth p ∨ ¬ Truth p`
* **Evaluative**: `EM_Eval Eval Γ := ∀ φ, Eval Γ φ ∨ ¬ Eval Γ φ`
Mathematically, EM becomes an **access property** (of a `Truth` or `Eval` instance), effectively an invariant of the model or interpreter.

## 2. Structural Gap via Operator Kernel
The algebraic core emerges when "stabilization" is presented as **kernel membership** of a cumulative operator:
* **Evaluative Scheme**: `upE Eval Γ s n := ∃ k ≤ n, Eval Γ (s k)`
* **Kernel Identity**: `upE Eval Γ s = botE ↔ StabilizesE Eval Γ s`
This transforms the Σ/Π asymmetry into **operator geometry** (kernel vs signal), where the Π₁ side is an algebraic kernel criterion.

## 3. Localization of Power (Dependency Order)
The file formalizes "constant-sequence" implications that localize exactly what forces what:
* **Semantics**: `LPO_Truth Truth → EM_Truth Truth` (via constant trace)
* **Evaluation**: `LPO_Eval Eval Γ → EM_Eval Eval Γ` (via constant sequence)
* **Trace Schema**: `DichotomyE Eval Γ` is definitionally `LPO_Eval Eval Γ`

The **full equivalence** "Total Dichotomy ↔ EM" is carried by the degenerate instance `Trace := ℕ → Prop` (where `Truth := id`), confirming that quantifying over arbitrary Prop-traces reinjects EM.

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
-- 2b. Evaluative Trace Schema (parallel to Base layer)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
We now lift the full trace/halting/stabilization schema to the evaluator level.

Given:
- `Eval : List Sentence → Sentence → Prop` (syntax-driven evaluation)
- `Γ : List Sentence` (context)
- `s : ℕ → Sentence` (sequence of sentences)

We define:
- `EvalTrace` : the trace induced by evaluating a sequence
- `upE` : cumulative closure on evaluative traces
- `HaltsE` : existential success (Σ₁)
- `StabilizesE` : universal failure (Π₁)
- `upE_eq_bot_iff` : kernel characterization
-/

section EvalTraceSchema

variable {Sentence : Type}

/-- The trace induced by evaluating a sequence of sentences -/
def EvalTrace (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) : ℕ → Prop :=
  fun n => Eval Γ (s n)

/-- Σ₁ evaluative: there exists a successful evaluation -/
def HaltsE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) : Prop :=
  ∃ n, Eval Γ (s n)

/-- Π₁ evaluative: all evaluations fail -/
def StabilizesE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) : Prop :=
  ∀ n, ¬ Eval Γ (s n)

/-- Cumulative closure on evaluative traces -/
def upE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) : ℕ → Prop :=
  fun n => ∃ k, k ≤ n ∧ Eval Γ (s k)

/-- upE is the up operator applied to EvalTrace -/
theorem upE_eq_up_EvalTrace (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    upE Eval Γ s = RevHalt.up (EvalTrace Eval Γ s) := rfl

/-- Signal invariance: HaltsE is preserved by upE -/
theorem exists_upE_iff (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    (∃ n, upE Eval Γ s n) ↔ HaltsE Eval Γ s := by
  unfold upE HaltsE
  constructor
  · intro ⟨n, k, _, hk⟩
    exact ⟨k, hk⟩
  · intro ⟨n, hn⟩
    exact ⟨n, n, Nat.le_refl n, hn⟩

/-- Bottom evaluative trace -/
def botE : ℕ → Prop := fun _ => False

/-- Kernel characterization (pointwise, 0 axiom) -/
theorem upE_bot_pointwise_iff (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    (∀ n, ¬ upE Eval Γ s n) ↔ StabilizesE Eval Γ s := by
  unfold upE StabilizesE
  constructor
  · intro h n hn
    have hup : ∃ k, k ≤ n ∧ Eval Γ (s k) := ⟨n, Nat.le_refl n, hn⟩
    exact h n hup
  · intro h n ⟨k, _, hk⟩
    exact h k hk

/-- Kernel characterization (equality form, uses propext) -/
theorem upE_eq_bot_iff (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    upE Eval Γ s = botE ↔ StabilizesE Eval Γ s := by
  unfold upE botE StabilizesE
  constructor
  · intro h n hn
    have : (∃ k, k ≤ n ∧ Eval Γ (s k)) = False := congrFun h n
    have hup : ∃ k, k ≤ n ∧ Eval Γ (s k) := ⟨n, Nat.le_refl n, hn⟩
    rw [this] at hup
    exact hup
  · intro h
    funext n
    apply propext
    constructor
    · intro ⟨k, _, hk⟩
      exact h k hk
    · intro hBot
      exact False.elim hBot

/-- StabilizesE ↔ ¬ HaltsE -/
theorem StabilizesE_iff_not_HaltsE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    StabilizesE Eval Γ s ↔ ¬ HaltsE Eval Γ s := by
  unfold StabilizesE HaltsE
  constructor
  · intro h ⟨n, hn⟩
    exact h n hn
  · intro h n hn
    exact h ⟨n, hn⟩

/-- The dichotomy on evaluative traces -/
def DichotomyE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) : Prop :=
  ∀ s : ℕ → Sentence, HaltsE Eval Γ s ∨ StabilizesE Eval Γ s

/-- DichotomyE is exactly LPO_Eval -/
theorem DichotomyE_iff_LPO_Eval (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    DichotomyE Eval Γ ↔ LPO_Eval Eval Γ := by
  unfold DichotomyE LPO_Eval HaltsE StabilizesE
  rfl

/-- upE monotonicity follows from base layer -/
theorem upE_mono (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    ∀ n m, n ≤ m → upE Eval Γ s n → upE Eval Γ s m := by
  intro n m hnm ⟨k, hkn, hk⟩
  exact ⟨k, Nat.le_trans hkn hnm, hk⟩

/-- Constructive double negation: ¬¬ DichotomyE holds -/
theorem dichotomyE_double_neg (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) (s : ℕ → Sentence) :
    ¬¬ (HaltsE Eval Γ s ∨ StabilizesE Eval Γ s) := by
  intro h
  apply h
  right
  intro n hn
  apply h
  left
  exact ⟨n, hn⟩

end EvalTraceSchema

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
-- Evaluative Trace Schema:
#print axioms RevHalt.RelativeFoundations.upE_eq_up_EvalTrace
#print axioms RevHalt.RelativeFoundations.exists_upE_iff
-- Pointwise kernel (0 axiom):
#print axioms RevHalt.RelativeFoundations.upE_bot_pointwise_iff
-- Equality kernel (requires propext):
#print axioms RevHalt.RelativeFoundations.upE_eq_bot_iff
#print axioms RevHalt.RelativeFoundations.StabilizesE_iff_not_HaltsE
#print axioms RevHalt.RelativeFoundations.DichotomyE_iff_LPO_Eval
#print axioms RevHalt.RelativeFoundations.upE_mono
#print axioms RevHalt.RelativeFoundations.dichotomyE_double_neg
-- Degenerate case:
#print axioms RevHalt.RelativeFoundations.Base_Is_Degenerate
#print axioms RevHalt.RelativeFoundations.Halts_Is_Degenerate
