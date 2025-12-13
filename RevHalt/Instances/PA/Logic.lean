/-
  RevHalt.Instances.PA.Logic

  Logic interface for Peano Arithmetic.

  ## Status: SKELETON

  This file needs to be completed with an actual PA formalization.
  Options:
  1. Use lean4-logic2 (https://github.com/hmonroe/lean4-logic2)
  2. Use Mathlib's computability theory directly
  3. Define a minimal first-order arithmetic

  ## Design Choices

  - NO AXIOMS: Use `sorry` for unproven lemmas (clearly marked as TODO)
  - This allows the file to compile while indicating incomplete proofs

  ## Required Definitions

  - `PropT` : Type of formulas/sentences
  - `Provable : PropT → Prop` : Derivability in PA
  - `Truth : PropT → Prop` : Satisfaction in the standard model ℕ
  - `Not : PropT → PropT` : Negation
  - `FalseP : PropT` : The false sentence
  - Soundness, consistency, absurd, truth_not_iff lemmas
-/
import RevHalt.Unified
import Mathlib.Computability.PartrecCode

namespace RevHalt.Instances.PA
open RevHalt_Unified
open Nat.Partrec

-- ==============================================================================================
-- Sentence Type (Placeholder - to be replaced with real PA formalization)
-- ==============================================================================================

/-- First-order arithmetic sentences.
    TODO: Replace with actual LO.FirstOrder.Sentence or similar. -/
inductive PASentence
| Halt (code : ℕ) : PASentence      -- Σ₁ sentence "code halts on input 0"
| Not (s : PASentence) : PASentence
| And (s1 s2 : PASentence) : PASentence
| Or (s1 s2 : PASentence) : PASentence
| Impl (s1 s2 : PASentence) : PASentence
| TrueS : PASentence
| FalseS : PASentence

-- ==============================================================================================
-- Truth Semantics (Standard Model ℕ)
-- ==============================================================================================

/-- Halting on input 0 via Partrec (used for Truth semantics). -/
def haltsOnZero (code : ℕ) : Prop :=
  (Code.eval (Denumerable.ofNat Code code) 0).Dom

/-- Truth in the standard model ℕ.
    This is the semantic interpretation. -/
def PATruth : PASentence → Prop
| PASentence.Halt code => haltsOnZero code
| PASentence.Not s => ¬PATruth s
| PASentence.And s1 s2 => PATruth s1 ∧ PATruth s2
| PASentence.Or s1 s2 => PATruth s1 ∨ PATruth s2
| PASentence.Impl s1 s2 => PATruth s1 → PATruth s2
| PASentence.TrueS => True
| PASentence.FalseS => False

-- ==============================================================================================
-- Provability (Derivability in PA)
-- ==============================================================================================

/-- Derivability in PA.
    TODO: Replace with actual proof predicate.
    For now: EMPTY provability (safe, sound, but trivial). -/
def PAProvable : PASentence → Prop := fun _ => False

-- ==============================================================================================
-- Negation and False
-- ==============================================================================================

/-- Negation. -/
def PANot : PASentence → PASentence := PASentence.Not

/-- False sentence. -/
def PAFalse : PASentence := PASentence.FalseS

-- ==============================================================================================
-- Logic Lemmas (NO AXIOMS - use sorry where needed)
-- ==============================================================================================

/-- Soundness: PA ⊢ σ → ℕ ⊧ σ.
    With empty provability, this is trivially true. -/
lemma pa_soundness : ∀ p, PAProvable p → PATruth p := by
  intro p hp
  exact False.elim hp

/-- Consistency: PA ⊬ ⊥.
    With empty provability, this is trivially true. -/
lemma pa_consistent : ¬PAProvable PAFalse := by
  intro hp
  exact hp

/-- Absurdity: PA ⊢ p → PA ⊢ ¬p → PA ⊢ ⊥.
    With empty provability, this is trivially true. -/
lemma pa_absurd : ∀ p, PAProvable p → PAProvable (PANot p) → PAProvable PAFalse := by
  intro p hp _
  exact hp

/-- truth_not_iff for classical semantics. -/
lemma pa_truth_not_iff : ∀ p, PATruth (PANot p) ↔ ¬PATruth p := by
  intro p
  rfl

/-- Truth(FalseS) = False. -/
lemma pa_truth_false : ¬PATruth PAFalse := by
  intro h
  exact h

-- ==============================================================================================
-- SoundLogicDef Instance
-- ==============================================================================================

/-- SoundLogicDef instance for PA. -/
def PALogicDef : SoundLogicDef PASentence where
  Provable := PAProvable
  Truth := PATruth
  soundness := pa_soundness
  Not := PANot
  FalseP := PAFalse
  consistent := pa_consistent
  absurd := pa_absurd
  truth_not_iff := pa_truth_not_iff

end RevHalt.Instances.PA
