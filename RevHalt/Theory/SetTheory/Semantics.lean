import Mathlib.Tactic.Tauto
import RevHalt.Theory.SetTheory.Deduction
import RevHalt.Theory.SetTheory.Formula

/-!
# RevHalt.Theory.SetTheory.Semantics

Defines Tarski Semantics for First-Order Logic (Model Theory).
Replaces axiomatic truth with constructive satisfiability.

## Definitions
- `Structure D`: Domain D with interpretation of `∈`.
- `Valuation D`: Mapping from variables to D.
- `Satisfies M val φ`: Tarski truth definition.
- `Model M Γ`: M satisfies all formulas in Γ.

## Theorems
- `Soundness`: If Γ ⊢ φ, then for all models M of Γ, M ⊨ φ.
-/

namespace RevHalt.SetTheory

open Formula Term

/--
  A Structure for the language {∈} consists of a domain and a membership relation.
  Equality is interpreted as actual equality in D.
-/
structure Structure (D : Type) where
  mem : D → D → Prop

/-- Variable assignment. -/
def Valuation (D : Type) := Nat → D

/-- Update valuation: val[0 ↦ x], shifting others by 1. -/
def vcons {D : Type} (x : D) (val : Valuation D) : Valuation D :=
  fun n => match n with
  | 0 => x
  | n+1 => val n

/-- Evaluation of Terms. -/
def eval_term {D : Type} (val : Valuation D) (t : Term) : D :=
  match t with
  | var k => val k

/-- Tarski Truth Definition. -/
def satisfies {D : Type} (M : Structure D) (val : Valuation D) (φ : Formula) : Prop :=
  match φ with
  | mem t1 t2 => M.mem (eval_term val t1) (eval_term val t2)
  | eq t1 t2  => (eval_term val t1) = (eval_term val t2)
  | fal       => False
  | imp p q   => satisfies M val p → satisfies M val q
  | all p     => ∀ (x : D), satisfies M (vcons x val) p

/-- M is a Model of Γ. -/
def IsModel {D : Type} (M : Structure D) (Γ : Set Formula) : Prop :=
  ∀ φ ∈ Γ, ∀ val, satisfies M val φ

-- =====================================================================================
-- Soundness Theorem
-- =====================================================================================

/--
  Logical Validity: True in all structures.
-/
def Valid (φ : Formula) : Prop :=
  ∀ {D : Type} (M : Structure D) (val : Valuation D), satisfies M val φ

/--
  Soundness: Derivability implies Semantic Consequence.
  Γ ⊢ φ → (∀ M, M ⊨ Γ → M ⊨ φ)
-/
theorem Soundness {Γ : Set Formula} {φ : Formula} (h : Derives Γ φ) :
    ∀ {D : Type} (M : Structure D), IsModel M Γ → ∀ val, satisfies M val φ := by
  intro D M hModel

  induction h with
  | hyp hp =>
      intro val
      exact hModel _ hp val
  | log hl =>
      intro val
      -- Helper Lemmas for Substitution and Lifting
      have hSubst : ∀ (t : Term) (φ : Formula),
          satisfies M val (subst0 t φ) ↔ satisfies M (vcons (eval_term val t) val) φ := sorry

      have hLift : ∀ (φ : Formula) (x : D),
          satisfies M (vcons x val) (lift0 1 φ) ↔ satisfies M val φ := sorry

      induction hl with
      | K p q =>
        dsimp only [satisfies]
        intro hp _
        exact hp
      | S p q r =>
        dsimp only [satisfies]
        intro hpqr hpq hp
        exact (hpqr hp) (hpq hp)
      | C p q =>
        dsimp only [satisfies, RevHalt.SetTheory.not] -- unfold not
        intro hnpnq hq
        apply Classical.byContradiction; intro hnp
        have hnq := hnpnq hnp
        exact hnq hq
      | I t φ =>
        intro hall
        rw [hSubst]
        exact hall (eval_term val t)
      | D p q =>
        intro hallpq hallp x
        exact (hallpq x) (hallp x)
      | V p =>
        intro hp x
        rw [hLift]
        exact hp
      | Ref =>
        exact rfl
      | Eq t1 t2 =>
        intro heq
        -- Decompose 'and' manually
        have hAndSat : ∀ A B, satisfies M val (RevHalt.SetTheory.and A B) ↔ (satisfies M val A ∧ satisfies M val B) := by
          intro A B
          dsimp [RevHalt.SetTheory.and, RevHalt.SetTheory.not, Formula.imp, satisfies]
          tauto

        rw [hAndSat]
        constructor
        · -- Case 1: ∀x (x ∈ t1 ↔ x ∈ t2)
          dsimp only [satisfies] -- unfolds 'all'
          intro x
          dsimp [RevHalt.SetTheory.iff, RevHalt.SetTheory.and, RevHalt.SetTheory.not, Formula.imp, satisfies]
          -- Now we can define hLiftT in range of x
          have hLiftT : ∀ t, eval_term (vcons x val) (lift_term 1 0 t) = eval_term val t := by
             intro t; cases t; simp [lift_term, vcons, eval_term, Nat.not_lt_zero]
          rw [hLiftT, hLiftT, heq]
          tauto
        · -- Case 2: ∀x (t1 ∈ x ↔ t2 ∈ x)
          dsimp only [satisfies]
          intro x
          dsimp [RevHalt.SetTheory.iff, RevHalt.SetTheory.and, RevHalt.SetTheory.not, Formula.imp, satisfies]
          have hLiftT : ∀ t, eval_term (vcons x val) (lift_term 1 0 t) = eval_term val t := by
             intro t; cases t; simp [lift_term, vcons, eval_term, Nat.not_lt_zero]
          rw [hLiftT, hLiftT, heq]
          tauto

  | mp hImp hP ihImp ihP =>
      intro val
      have hImpV := ihImp val
      have hPV := ihP val
      exact hImpV hPV
  | gen hP ih =>
      intro val x
      apply ih (vcons x val)

end RevHalt.SetTheory
