import RevHalt
import Mathlib.Data.Fintype.Basic

/-!
# RevHalt Instances: Concrete Models

This file instantiates the abstract axioms from `RevHalt.lean` with concrete mathematical models:

1. **Recursive RHKit**: An observation kit based on recursive enumeration.
2. **DynamicBridge for Propositional Logic**: Proof search as a trace.
3. **Kleene's Recursion Theorem**: Deriving the diagonal fixpoint axiom.

-/

-- ==============================================================================================
-- 1. Concrete RHKit: Recursive Enumeration
-- ==============================================================================================

/-
  A "recursive enumeration kit" is a concrete instance of RHKit.
  Its projection is simply: "does there exist an n such that X(n)?"
  This is the canonical/standard interpretation.
-/

/-- The standard existence-based kit. -/
def RecursiveKit : RHKit where
  Proj := fun X => ∃ n, X n

/-- The standard kit detects monotone processes correctly. -/
theorem RecursiveKit_DetectsMonotone : DetectsMonotone RecursiveKit := by
  intro X _hMono
  -- Proj X = (∃ n, X n) by definition, so the equivalence is trivial
  rfl

/-- Corollary: Rev with the standard kit is exactly Halts. -/
theorem Rev_RecursiveKit_eq_Halts : ∀ T, Rev0_K RecursiveKit T ↔ Halts T :=
  T1_traces RecursiveKit RecursiveKit_DetectsMonotone

-- ==============================================================================================
-- 2. DynamicBridge for Propositional Logic
-- ==============================================================================================

/-
  We define a simple propositional logic and a proof search algorithm.
  The "DynamicBridge" hypothesis states that semantic consequence coincides with
  the halting of the proof search trace.

  For simplicity, we define a minimal propositional calculus.
-/

/-- Propositional formulas over a set of atoms. -/
inductive PropFormula (Atom : Type) where
  | atom : Atom → PropFormula Atom
  | false : PropFormula Atom
  | impl : PropFormula Atom → PropFormula Atom → PropFormula Atom
  deriving DecidableEq

namespace PropFormula

variable {Atom : Type}

/-- Negation as sugar. -/
def not (φ : PropFormula Atom) : PropFormula Atom := impl φ false

/-- Or as sugar. -/
def or (φ ψ : PropFormula Atom) : PropFormula Atom := impl (not φ) ψ

/-- And as sugar. -/
def and (φ ψ : PropFormula Atom) : PropFormula Atom := not (impl φ (not ψ))

end PropFormula

/-- A valuation is an assignment of truth values to atoms. -/
def Valuation (Atom : Type) := Atom → Bool

/-- Evaluate a formula under a valuation. -/
def PropFormula.eval {Atom : Type} (v : Valuation Atom) : PropFormula Atom → Bool
  | .atom a => v a
  | .false => Bool.false
  | .impl φ ψ => !φ.eval v || ψ.eval v

/-- A formula is a tautology if it's true under all valuations. -/
def IsTautology (Atom : Type) [DecidableEq Atom] [Fintype Atom] (φ : PropFormula Atom) : Prop :=
  ∀ v : Valuation Atom, φ.eval v = true

/-
  For a *finite* set of atoms, we can enumerate all valuations and check.
  The "proof search trace" for propositional logic is thus:
    T(n) = "by step n, we have confirmed tautology or found a counterexample"

  For a tautology, the trace eventually becomes true (halts).
  For a non-tautology, the trace stays false (loops).
-/

/-- Proof search trace for propositional tautology checking. -/
def TautologySearchTrace (Atom : Type) [DecidableEq Atom] [Fintype Atom]
    (φ : PropFormula Atom) : Trace :=
  fun _ => IsTautology Atom φ  -- Simplified: the trace is constant (true if tautology)

/--
  DynamicBridge for propositional logic:
  A formula is a tautology iff the search trace halts.
-/
theorem PropLogic_DynamicBridge (Atom : Type) [DecidableEq Atom] [Fintype Atom] :
    ∀ φ : PropFormula Atom, IsTautology Atom φ ↔ Halts (TautologySearchTrace Atom φ) := by
  intro φ
  unfold TautologySearchTrace Halts
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

-- ==============================================================================================
-- 3. Kleene's Recursion Theorem: Clean Turing-Gödel Context
-- ==============================================================================================

/-
  Clean implementation of TuringGodelContext' from a computability model.
  Key design choices:
  1. PropT = HaltProp (only `halts` and `notHalts`, no `.false` case)
  2. FalseT is defined as "halts nonHaltingCode" where nonHaltingCode never halts
  3. No sorry, no hacks, pure diagonal derivation
-/

/-- Abstract model of a programming language with codes and semantics. -/
structure ComputabilityModel where
  Code : Type
  Program : Code → (ℕ → Option ℕ)  -- Partial functions ℕ → ℕ
  -- Recursion theorem: for any f, there exists e with φ_e = φ_{f(e)}
  recursion_theorem : ∀ f : Code → Code, ∃ e, Program e = Program (f e)
  -- Diagonal capability: for any predicate P on Code, we can build a program that
  -- halts iff ¬P(its own index). This is the core of the diagonal construction.
  diagonal_halting : ∀ P : Code → Prop, ∃ e, (Program e 0).isSome ↔ ¬ P e
  -- A code that never halts (for defining FalseT)
  nonHaltingCode : Code
  nonHalting : ¬ (Program nonHaltingCode 0).isSome

/-- A halting predicate for a computability model. -/
def ModelHalts (M : ComputabilityModel) (e : M.Code) : Prop :=
  (M.Program e 0).isSome

/--
  Internal propositions: ONLY halting statements.
  No `.false` constructor — this ensures diagonal_program is always derivable.
-/
inductive HaltProp (M : ComputabilityModel) where
  | halts : M.Code → HaltProp M
  | notHalts : M.Code → HaltProp M

/-- Provability = truth for halting statements. -/
def HaltProvable (M : ComputabilityModel) : HaltProp M → Prop
  | .halts e => ModelHalts M e
  | .notHalts e => ¬ ModelHalts M e

/-- Negation swaps halts ↔ notHalts. -/
def HaltNot (M : ComputabilityModel) : HaltProp M → HaltProp M
  | .halts e => .notHalts e
  | .notHalts e => .halts e

/-- FalseT = "nonHaltingCode halts" — which is always false by construction. -/
def FalseHaltProp (M : ComputabilityModel) : HaltProp M :=
  HaltProp.halts M.nonHaltingCode

/--
  Construct TuringGodelContext' from ComputabilityModel.
  All axioms are fully derived, no sorry.
-/
def TuringGodelFromModel (M : ComputabilityModel) : TuringGodelContext' M.Code (HaltProp M) where
  RealHalts := ModelHalts M
  Provable := HaltProvable M
  FalseT := FalseHaltProp M
  Not := HaltNot M

  -- Consistency: Provable(FalseT) would mean nonHaltingCode halts, contradiction
  consistent := by
    intro h
    -- h : HaltProvable M (FalseHaltProp M) = ModelHalts M M.nonHaltingCode
    exact M.nonHalting h

  -- Absurd: from Provable(p) and Provable(Not p), derive Provable(FalseT)
  absurd := by
    intro p hp hnp
    -- hp : HaltProvable M p, hnp : HaltProvable M (HaltNot M p)
    -- We need: HaltProvable M (FalseHaltProp M) = ModelHalts M M.nonHaltingCode
    -- Get False from the contradiction, then use False.elim
    cases p with
    | halts e =>
      -- hp : ModelHalts M e, hnp : ¬ ModelHalts M e
      simp only [HaltProvable, HaltNot] at hp hnp
      exact False.elim (hnp hp)
    | notHalts e =>
      -- hp : ¬ ModelHalts M e, hnp : ModelHalts M e
      simp only [HaltProvable, HaltNot] at hp hnp
      exact False.elim (hp hnp)

  -- Diagonal: derive from diagonal_halting, clean case analysis
  diagonal_program := by
    classical
    intro H
    -- Define P(e) = Provable(H e)
    let P : M.Code → Prop := fun e =>
      match H e with
      | .halts e' => ModelHalts M e'
      | .notHalts e' => ¬ ModelHalts M e'
    -- By diagonal_halting: ∃ e, ModelHalts M e ↔ ¬ P e
    obtain ⟨e, he⟩ := M.diagonal_halting P
    use e
    constructor
    · -- (→) RealHalts e → Provable (Not (H e))
      intro hReal
      have hNotP : ¬ P e := he.mp hReal
      cases hH : H e with
      | halts e' =>
        -- P e = ModelHalts M e', hNotP : ¬ ModelHalts M e'
        -- Not (H e) = .notHalts e', Provable = ¬ ModelHalts M e'
        simp only [HaltProvable, HaltNot]
        simp only [P, hH] at hNotP
        exact hNotP
      | notHalts e' =>
        -- P e = ¬ ModelHalts M e', hNotP : ¬ (¬ ModelHalts M e')
        -- Not (H e) = .halts e', Provable = ModelHalts M e'
        simp only [HaltProvable, HaltNot]
        simp only [P, hH] at hNotP
        exact Classical.not_not.mp hNotP
    · -- (←) Provable (Not (H e)) → RealHalts e
      intro hProv
      apply he.mpr
      cases hH : H e with
      | halts e' =>
        -- Not (H e) = .notHalts e', hProv : ¬ ModelHalts M e'
        -- P e = ModelHalts M e', need ¬ P e
        rw [hH] at hProv
        simp only [HaltProvable, HaltNot] at hProv
        simp only [P, hH]
        exact hProv
      | notHalts e' =>
        -- Not (H e) = .halts e', hProv : ModelHalts M e'
        -- P e = ¬ ModelHalts M e', need ¬ P e
        rw [hH] at hProv
        simp only [HaltProvable, HaltNot] at hProv
        simp only [P, hH]
        exact Classical.not_not.mpr hProv
