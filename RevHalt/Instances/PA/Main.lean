/-
  RevHalt.Instances.PA.Main

  Entry point for the PA instance.
  Assembles all components and invokes the Master Theorem.

  ## Status

  This file assembles the complete PA pipeline:
  - PAModel : RigorousModel
  - PAKit : RHKit
  - PALogicEncodedCoded : SoundLogicEncodedCoded

  Then invokes RevHalt_Master_Complete_Coded.
-/
import RevHalt.Instances.PA.Kit
import RevHalt.Instances.PA.Arithmetization
import RevHalt.Unified.Coded.Master

namespace RevHalt.Instances.PA
open RevHalt_Unified
open RevHalt_Unified.Coded

-- ==============================================================================================
-- Halting Encoding Package
-- ==============================================================================================

/-- HaltingEncoding instance for PA.
    Connects RMHalts PAModel to PATruth via PAHaltEncode. -/
def PAHaltingEncoding : HaltingEncoding PAModel PASentence PALogicDef where
  HaltEncode := PAHaltEncode
  encode_correct := by
    intro e
    -- RMHalts PAModel e = ∃ t, (PAProgram e t).isSome
    -- PATruth (PAHaltEncode e) = PATruth (Halt e) = haltsOnZero e = PAHalts e
    simp only [RMHalts, PAModel]
    exact pa_halts_iff_exists_time e

-- ==============================================================================================
-- Full Package: SoundLogicEncodedCoded
-- ==============================================================================================

/-- Complete SoundLogicEncodedCoded instance for PA.
    Packages: FC + Logic (L) + Arithmetization (A) + HaltEncoding (E). -/
def PALogicEncodedCoded : SoundLogicEncodedCoded PAModel PASentence where
  FC := PAFamilyCoding
  Logic := PALogicDef
  Arith := PAArith
  HaltE := PAHaltingEncoding

-- ==============================================================================================
-- H_code: Code for the Halting Formula Family
-- ==============================================================================================

/-- H_code: The code in PAGCode that represents the halting family.
    PAEvalG (n+2) _ = Halt n, so for identity (e ↦ Halt e), we need
    a family where evalG g e = Halt e.

    Current PAEvalG doesn't support this directly (it's (n+2) ↦ Halt n for all inputs).
    We need to extend PAEvalG to support identity families.

    For now, use a placeholder. -/
def PA_H_code : PAGCode := 0  -- Placeholder

/-- Proof that evalG PA_H_code e = PAHaltEncode e.
    This requires extending PAEvalG to support identity families.
    TODO: Implement proper PAEvalG with identity support. -/
lemma pa_H_code_correct : ∀ e, PAFamilyCoding.evalG PA_H_code e = PAHaltEncode e := by
  intro e
  -- Current PAEvalG 0 _ = FalseS, but we need Halt e
  -- This is a limitation of our simple PAEvalG definition
  sorry  -- TODO: Extend PAEvalG to support identity families

-- ==============================================================================================
-- Master Theorem for PA
-- ==============================================================================================

/-- **MASTER THEOREM FOR PA (CODED)**

    Proves T1 + Diagonal for PA.

    Note: pa_H_code_correct has a sorry - needs proper PAEvalG extension. -/
theorem PA_Master_Theorem :
    let ctx := EnrichedContextCoded_from_RM PAModel PAKit pa_kit_correct PALogicEncodedCoded
    -- (1) T1: RealHalts matches Truth of H
    (∀ e, ctx.RealHalts e ↔ ctx.Truth (ctx.H e)) ∧
    -- (2) Diagonal for H_code
    (∃ e, ctx.RealHalts e ↔ ctx.Provable (ctx.Not (ctx.H e))) :=
  RevHalt_Master_Complete_Coded PAModel PAKit pa_kit_correct PALogicEncodedCoded
    PA_H_code pa_H_code_correct

-- ==============================================================================================
-- Verification
-- ==============================================================================================

#check PA_Master_Theorem
#print axioms PA_Master_Theorem

end RevHalt.Instances.PA
