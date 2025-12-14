/-
  RevHalt.Instances.PA.Arithmetization

  Coded Arithmetization for PA using PRModel from Instances.Arithmetization.

  ## Key Design

  - REUSES `PRModel` from `Instances.Arithmetization` (proven without sorry)
  - Adds `PAFamilyCoding` for coded formula families
  - Handles non-trivial provability correctly

  ## No sorry, no noncomputable, no axiom
-/
import RevHalt.Instances.PA.Logic
import RevHalt.Instances.Arithmetization
import RevHalt.Bridge.Coded.Interface

namespace RevHalt.Instances.PA

open RevHalt.Coded
open Nat.Partrec
open RevHalt.Instances.Arithmetization

-- ==============================================================================================
-- Family Coding for PA (with identity support)
-- ==============================================================================================

/-- GCode: codes for formula families.

    Encoding:
    - g = 0: Identity family (e ↦ Halt (encode e))
    - g = 1: Constant FalseS
    - g = 2: Constant TrueS
    - g = n+3: Constant Halt(n) for all inputs -/
abbrev PAGCode := ℕ

/-- Evaluate a coded formula family. -/
def PAEvalG : PAGCode → PRCode → PASentence
| 0, e => PASentence.Halt (Encodable.encode e)  -- Identity
| 1, _ => PASentence.FalseS                      -- Constant False
| 2, _ => PASentence.TrueS                       -- Constant True
| (n + 3), _ => PASentence.Halt n                -- Constant Halt(n)

/-- FamilyCoding instance using PRCode. -/
def PAFamilyCoding : FamilyCoding PRCode PASentence where
  GCode := PAGCode
  evalG := PAEvalG

-- ==============================================================================================
-- Halting Code for repr_provable_not_coded
-- ==============================================================================================

/-- A code that halts on any input: Code.zero always returns 0 immediately. -/
def haltingCode : PRCode := Code.zero

/-- haltingCode halts on any input. -/
lemma halting_code_halts : ∀ n, PRHalts haltingCode n := by
  intro n
  -- Code.eval Code.zero n = Part.some n, and (Part.some n).Dom = True
  trivial

-- ==============================================================================================
-- Arithmetization (Coded) - handling non-trivial provability
-- ==============================================================================================

/-- Helper: Compute whether PAProvable (Not (PAEvalG g e)) is True or False.
    This determines which predicate code to use. -/
def provableNotEvalG (g : PAGCode) : Bool :=
  match g with
  | 1 => true   -- Not FalseS is provable
  | _ => false  -- Everything else: Not (evalG g e) is not provable

/-- repr_provable_not_coded for non-trivial provability.

    Case analysis on g:
    - g = 0: Not(Halt(encode e)) not provable → use loopCode
    - g = 1: Not(FalseS) IS provable → use haltingCode
    - g = 2: Not(TrueS) not provable → use loopCode
    - g = n+3: Not(Halt n) not provable → use loopCode -/
theorem pa_repr_provable_not_coded :
    ∀ g : PAGCode, ∃ pc : PRModel.PredCode,
      ∀ e : PRModel.Code, PRModel.PredDef pc e ↔ PALogicDef.Provable (PALogicDef.Not (PAEvalG g e)) := by
  intro g
  haveI : Encodable PRModel.Code := inferInstanceAs (Encodable PRCode)

  match g with
  | 0 =>
    -- evalG 0 e = Halt(encode e)
    -- Not(Halt(encode e)) is not provable
    use loopCode
    intro e
    simp only [PRModel, PAEvalG, PALogicDef, PANot, PAProvable]
    constructor
    · intro h; exact pr_loop_non_halting (Encodable.encode e) h
    · intro h; exact False.elim h

  | 1 =>
    -- evalG 1 e = FalseS
    -- Not(FalseS) IS provable (= True)
    -- So we need PredDef pc e ↔ True, i.e., pc halts on encode e
    use haltingCode
    intro e
    simp only [PRModel, PAEvalG, PALogicDef, PANot, PAProvable]
    constructor
    · intro _; trivial
    · intro _; exact halting_code_halts (Encodable.encode e)

  | 2 =>
    -- evalG 2 e = TrueS
    -- Not(TrueS) is not provable
    use loopCode
    intro e
    simp only [PRModel, PAEvalG, PALogicDef, PANot, PAProvable]
    constructor
    · intro h; exact pr_loop_non_halting (Encodable.encode e) h
    · intro h; exact False.elim h

  | (n + 3) =>
    -- evalG (n+3) e = Halt n
    -- Not(Halt n) is not provable
    use loopCode
    intro e
    simp only [PRModel, PAEvalG, PALogicDef, PANot, PAProvable]
    constructor
    · intro h; exact pr_loop_non_halting (Encodable.encode e) h
    · intro h; exact False.elim h

/-- ArithmetizationCoded instance for PA using PRModel. -/
def PAArith : ArithmetizationCoded PRModel PASentence PALogicDef PAFamilyCoding where
  repr_provable_not_coded := pa_repr_provable_not_coded

end RevHalt.Instances.PA
