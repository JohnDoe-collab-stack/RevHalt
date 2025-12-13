/-
  RevHalt.Instances.PA.Arithmetization

  Coded Arithmetization for PA using PRModel from Instances.Arithmetization.

  ## Key Design

  - REUSES `PRModel` from `Instances.Arithmetization` (proven without sorry)
  - Adds `PAFamilyCoding` for coded formula families
  - Adds `PAArith` : ArithmetizationCoded instance

  ## No sorry, no noncomputable, no axiom
-/
import RevHalt.Instances.PA.Logic
import RevHalt.Instances.Arithmetization
import RevHalt.Unified.Coded.Interface

namespace RevHalt.Instances.PA
open RevHalt_Unified
open RevHalt_Unified.Coded
open Nat.Partrec
open RevHalt.Instances.Arithmetization

-- ==============================================================================================
-- Family Coding for PA (with identity support)
-- ==============================================================================================

/-- GCode: codes for formula families.
    A code g represents a computable function e ↦ formula.

    Encoding (using PRCode = Code directly):
    - g = 0: Identity family (e ↦ Halt (encode e))
    - g = 1: Constant FalseS
    - g = 2: Constant TrueS
    - g encodes (3, c): Constant Halt(encode c) for all inputs -/
abbrev PAGCode := ℕ

/-- Evaluate a coded formula family.
    Uses PRCode (= Nat.Partrec.Code) as the code type. -/
def PAEvalG : PAGCode → PRCode → PASentence
| 0, e => PASentence.Halt (Encodable.encode e)  -- Identity: e ↦ Halt(encode e)
| 1, _ => PASentence.FalseS                      -- Constant False
| 2, _ => PASentence.TrueS                       -- Constant True
| (n + 3), _ => PASentence.Halt n                -- Constant Halt(n) for all e

/-- FamilyCoding instance using PRCode. -/
def PAFamilyCoding : FamilyCoding PRCode PASentence where
  GCode := PAGCode
  evalG := PAEvalG

-- ==============================================================================================
-- PATruth for PRCode (bridge to PA semantics)
-- ==============================================================================================

/-- PATruth (Halt n) should match PRHalts (ofNat n) 0.
    We need to verify the connection. -/
lemma pa_truth_halt_equiv (n : ℕ) :
    PATruth (PASentence.Halt n) ↔ PRHalts (Denumerable.ofNat Code n) 0 := by
  rfl  -- By definition of PATruth and haltsOnZero

-- ==============================================================================================
-- Arithmetization (Coded) - using PRModel
-- ==============================================================================================

/-- For PA with empty provability (PAProvable = False), repr_provable_not_coded is trivial:
    Provable (Not (evalG g e)) = False for all g, e
    So we need: PRModel.PredDef pc e ↔ False
    i.e., ¬PRHalts pc (encode e) for all e

    Solution: Use loopCode from Arithmetization.lean which never halts on any input. -/
theorem pa_repr_provable_not_coded :
    ∀ g : PAGCode, ∃ pc : PRModel.PredCode,
      ∀ e : PRModel.Code, PRModel.PredDef pc e ↔ PALogicDef.Provable (PALogicDef.Not (PAEvalG g e)) := by
  intro g
  -- Since PALogicDef.Provable = PAProvable = (fun _ => False), we need:
  -- PRModel.PredDef pc e ↔ False
  -- i.e., PRPredDef pc e ↔ False
  -- i.e., ¬PRHalts pc (encode e) for all e

  -- Use loopCode which never halts on ANY input
  use loopCode
  intro e
  -- PRModel.Code = PRCode = Code, which is Encodable
  haveI : Encodable PRModel.Code := inferInstanceAs (Encodable PRCode)
  simp only [PRModel]
  constructor
  · intro h
    -- h : PRHalts loopCode (encode e)
    exact pr_loop_non_halting (Encodable.encode e) h
  · intro h
    exact False.elim h

/-- ArithmetizationCoded instance for PA using PRModel. -/
def PAArith : ArithmetizationCoded PRModel PASentence PALogicDef PAFamilyCoding where
  repr_provable_not_coded := pa_repr_provable_not_coded

end RevHalt.Instances.PA
