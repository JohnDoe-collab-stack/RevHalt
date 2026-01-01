import RevHalt.Theory.RelativeFoundations

/-!
# LPO Relative to Formation Referential (R1)

This file formalizes the key missing abstraction: **LPO relative to a grammar of admissible sequences**.

## Core Insight

The standard `LPO_Eval` quantifies over **all** sequences `s : ℕ → Sentence`.
But in a referential framework, we only quantify over **admissible** sequences (those formable in R1).

This changes:
1. The logical strength of LPO (restricted LPO can be weaker)
2. The collapse condition (constant sequence trick requires `AdmitsConst`)
3. The hierarchy (more restrictive R1 → weaker LPO)

## Abstract Theory

This is abstract theory, independent of any specific dynamics.
For any dynamics that generates a restricted grammar:
- If `AdmitsConst` is FALSE, `LPO_R1` does NOT imply `EM_Eval` via the usual trick
- The hierarchy theorem relates different grammars

-/

namespace RevHalt.RelativeR1

variable {Sentence : Type}

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) LPO Relative to Grammar R1
-- ═══════════════════════════════════════════════════════════════════════════════

/-- LPO relative to a grammar of admissible sequences (R1).
    Only quantifies over sequences satisfying `Adm`. -/
def LPO_Eval_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ s, Adm s → (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))

/-- EM at evaluation level (imported from RelativeFoundations, renamed for clarity). -/
def EM_Eval (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) : Prop :=
  ∀ φ : Sentence, Eval Γ φ ∨ ¬ Eval Γ φ

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Collapse Condition: AdmitsConst
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A grammar `Adm` admits constant sequences.
    This is the condition for the "constant sequence trick" to work. -/
def AdmitsConst (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ φ, Adm (fun _ => φ)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Collapse Theorem: LPO_R1 → EM_Eval (conditional)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The constant sequence trick, but properly conditioned on R1 admitting constants.
    If R1 admits constant sequences, then LPO_R1 implies EM_Eval. -/
theorem LPO_R1_imp_EM_if_const
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop)
    (hConst : AdmitsConst Adm) :
    LPO_Eval_R1 Eval Γ Adm → EM_Eval Eval Γ := by
  intro hLPO φ
  -- The constant sequence (fun _ => φ) is admissible by hypothesis
  have hAdm : Adm (fun _ => φ) := hConst φ
  -- Apply LPO_R1 to this constant sequence
  have h := hLPO (fun _ => φ) hAdm
  cases h with
  | inl hex =>
    -- exists n, Eval Γ φ
    left
    exact hex.elim fun _ hx => hx
  | inr hall =>
    -- forall n, ¬ Eval Γ φ
    right
    exact hall 0

/-- The unconditional LPO_Eval is LPO_R1 with trivial grammar (all sequences admissible). -/
def AllAdm : (ℕ → Sentence) → Prop := fun _ => True

theorem AllAdm_admits_const : AdmitsConst (AllAdm (Sentence := Sentence)) := by
  intro _
  trivial

/-- Global LPO equals LPO_R1 with trivial grammar. -/
theorem LPO_Eval_eq_LPO_R1_All
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    RevHalt.RelativeFoundations.LPO_Eval Eval Γ ↔ LPO_Eval_R1 Eval Γ AllAdm := by
  constructor
  · intro h s _
    exact h s
  · intro h s
    exact h s trivial

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Hierarchy: Monotonicity on R1
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Monotonicity: if Adm₁ ⊆ Adm₂, then LPO on Adm₂ implies LPO on Adm₁.
    (Stronger grammar restriction → weaker LPO requirement) -/
theorem LPO_mono_R1
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm₁ Adm₂ : (ℕ → Sentence) → Prop)
    (hSub : ∀ s, Adm₁ s → Adm₂ s) :
    LPO_Eval_R1 Eval Γ Adm₂ → LPO_Eval_R1 Eval Γ Adm₁ := by
  intro h s hs1
  exact h s (hSub s hs1)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Non-Collapse: Examples of Grammars That Don't Admit Constants
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The empty grammar (no sequences admissible).
    LPO_R1 is trivially true, but gives no EM. -/
def EmptyAdm : (ℕ → Sentence) → Prop := fun _ => False

theorem LPO_R1_empty_trivial
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    LPO_Eval_R1 Eval Γ EmptyAdm := by
  intro s hs
  exact False.elim hs

theorem EmptyAdm_not_admits_const [Inhabited Sentence] :
    ¬ AdmitsConst (EmptyAdm (Sentence := Sentence)) := by
  intro h
  exact h default

/-- Changing sequences only: sequences where `s(n) ≠ s(n+1)` for all n.
    This grammar cannot admit constants. -/
def ChangingAdm (_Eval : List Sentence → Sentence → Prop) (_Γ : List Sentence)
    : (ℕ → Sentence) → Prop :=
  fun s => ∀ n, s n ≠ s (n + 1)

theorem ChangingAdm_not_admits_const [Inhabited Sentence]
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    ¬ AdmitsConst (ChangingAdm Eval Γ) := by
  intro h
  -- For any φ, the constant sequence should be in ChangingAdm
  -- But constant sequence has s(0) = s(1), contradiction
  have hConst : ChangingAdm Eval Γ (fun _ => default) := h default
  have hNeq : (fun _ => default) 0 ≠ (fun _ => default) 1 := hConst 0
  exact hNeq rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Link to Evaluative Trace Schema
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HaltsE relative to R1 -/
def HaltsE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (_Adm : (ℕ → Sentence) → Prop) (s : ℕ → Sentence) (_hAdm : _Adm s) : Prop :=
  ∃ n, Eval Γ (s n)

/-- StabilizesE relative to R1 -/
def StabilizesE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (_Adm : (ℕ → Sentence) → Prop) (s : ℕ → Sentence) (_hAdm : _Adm s) : Prop :=
  ∀ n, ¬ Eval Γ (s n)

/-- The dichotomy on admissible sequences -/
def DichotomyE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ s, Adm s → (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))

/-- DichotomyE_R1 is exactly LPO_Eval_R1 -/
theorem DichotomyE_R1_iff_LPO_R1
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) :
    DichotomyE_R1 Eval Γ Adm ↔ LPO_Eval_R1 Eval Γ Adm := by
  rfl

end RevHalt.RelativeR1

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.RelativeR1.LPO_R1_imp_EM_if_const
#print axioms RevHalt.RelativeR1.LPO_Eval_eq_LPO_R1_All
#print axioms RevHalt.RelativeR1.LPO_mono_R1
#print axioms RevHalt.RelativeR1.LPO_R1_empty_trivial
#print axioms RevHalt.RelativeR1.DichotomyE_R1_iff_LPO_R1
