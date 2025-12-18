/-
  RevHalt.Instances.PA.Main

  Entry point for the PA instance using PRModel.
  Assembles all components and invokes the Master Theorem.

  ## Key Design

  - Uses PRModel from Instances.Arithmetization (proven, no sorry)
  - PAFamilyCoding provides coded formula families
  - H_code = 0 gives identity family e ↦ Halt(encode e)

  ## No sorry, no noncomputable, no axiom
-/
import RevHalt.Instances.PA.Kit
import RevHalt.Instances.PA.Arithmetization
import RevHalt.Bridge.Coded.Master

namespace RevHalt.Instances.PA

open RevHalt.Coded
open Nat.Partrec
open RevHalt.Instances.Arithmetization

-- ==============================================================================================
-- Halting Encoding Package
-- ==============================================================================================

/-- HaltEncode for PRCode: e ↦ Halt(encode e). -/
def PAHaltEncode_PR (e : PRCode) : PASentence :=
  PASentence.Halt (Encodable.encode e)

/-- encode_correct: RMHalts PRModel e ↔ PATruth (PAHaltEncode_PR e).

    RMHalts PRModel e = ∃ t, (PRProgram_time e t).isSome ↔ PRHalts e 0
    PATruth (Halt (encode e)) = haltsOnZero (encode e)
                              = (eval (ofNat (encode e)) 0).Dom
                              = (eval e 0).Dom  [by ofNat ∘ encode = id]
                              = PRHalts e 0 -/
lemma pa_encode_correct_pr :
    ∀ e : PRCode, RMHalts PRModel e ↔ PALogicDef.Truth (PAHaltEncode_PR e) := by
  intro e
  simp only [RMHalts, PRModel, PAHaltEncode_PR, PALogicDef, PATruth, haltsOnZero]
  -- RMHalts PRModel e = ∃ t, (PRProgram_time e t).isSome
  -- PATruth (Halt (encode e)) = (eval (ofNat (encode e)) 0).Dom
  rw [Denumerable.ofNat_encode]
  exact halts0_iff_exists_time e

/-- HaltingEncoding instance for PRModel. -/
def PAHaltingEncoding : HaltingEncoding PRModel PASentence PALogicDef where
  HaltEncode := PAHaltEncode_PR
  encode_correct := pa_encode_correct_pr

-- ==============================================================================================
-- Full Package: SoundLogicEncodedCoded
-- ==============================================================================================

/-- Complete SoundLogicEncodedCoded instance for PA.
    Packages: FC + Logic (L) + Arithmetization (A) + HaltEncoding (E). -/
def PALogicEncodedCoded : SoundLogicEncodedCoded PRModel PASentence where
  FC := PAFamilyCoding
  Logic := PALogicDef
  Arith := PAArith
  HaltE := PAHaltingEncoding

-- ==============================================================================================
-- H_code: Code for the Halting Formula Family
-- ==============================================================================================

/-- H_code = 0: The identity family e ↦ Halt(encode e).
    By definition of PAEvalG 0 e = Halt (encode e) = PAHaltEncode_PR e. -/
def PA_H_code : PAGCode := 0

/-- Proof that evalG PA_H_code e = PAHaltEncode_PR e.
    This is direct by definition of PAEvalG. -/
lemma pa_H_code_correct : ∀ e, PAFamilyCoding.evalG PA_H_code e = PAHaltEncode_PR e := by
  intro e
  rfl  -- PAEvalG 0 e = Halt (encode e) = PAHaltEncode_PR e

-- ==============================================================================================
-- Master Theorem for PA
-- ==============================================================================================

/-- **MASTER THEOREM FOR PA (CODED)**

    Proves T1 + Diagonal for PA.
    NO sorry, NO noncomputable, NO axiom (except standard Mathlib). -/
theorem PA_Master_Theorem :
    let ctx := EnrichedContextCoded_from_RM PRModel PAKit pa_kit_correct PALogicEncodedCoded
    -- (1) T1: RealHalts matches Truth of H
    (∀ e, ctx.RealHalts e ↔ ctx.Truth (ctx.H e)) ∧
    -- (2) Diagonal for H_code
    (∃ e, ctx.RealHalts e ↔ ctx.Provable (ctx.Not (ctx.H e))) :=
  RevHalt_Master_Complete_Coded PRModel PAKit pa_kit_correct PALogicEncodedCoded
    PA_H_code pa_H_code_correct

-- ==============================================================================================
-- Verification
-- ==============================================================================================

#check PA_Master_Theorem
-- #print axioms PA_Master_Theorem

end RevHalt.Instances.PA
