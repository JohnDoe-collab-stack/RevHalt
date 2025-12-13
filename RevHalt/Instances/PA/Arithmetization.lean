/-
  RevHalt.Instances.PA.Arithmetization

  Coded Arithmetization for PA.

  ## Key Structure

  Uses `FamilyCoding` to represent computable formula families:
  - `GCode := ℕ` (codes for primitive recursive functions on formulas)
  - `evalG g e` = decode(F_g(e)) where F_g is the g-th PR function

  ## Main Theorem

  `pa_repr_provable_not_coded`:
    ∀ g : GCode, ∃ pc : PredCode,
      ∀ e, PredDef pc e ↔ Provable (Not (evalG g e))

  With empty provability, this is trivially satisfied by any non-halting code.
-/
import RevHalt.Instances.PA.Encoding
import RevHalt.Unified.Coded.Interface

namespace RevHalt.Instances.PA
open RevHalt_Unified
open RevHalt_Unified.Coded

-- ==============================================================================================
-- Family Coding for PA
-- ==============================================================================================

/-- GCode: codes for formula families.
    A code g represents a computable function e ↦ formula. -/
abbrev PAGCode := ℕ

/-- Evaluate a coded formula family.
    For simplicity, we define a minimal coding:
    - g = 0: Constant FalseS
    - g = 1: Constant TrueS
    - g = n+2: Halt(n) for all inputs (ignoring the input) -/
def PAEvalG : PAGCode → PACode → PASentence
| 0, _ => PASentence.FalseS
| 1, _ => PASentence.TrueS
| (n + 2), _ => PASentence.Halt n

/-- FamilyCoding instance for PA. -/
def PAFamilyCoding : FamilyCoding PACode PASentence where
  GCode := PAGCode
  evalG := PAEvalG

-- ==============================================================================================
-- Predicate Coding
-- ==============================================================================================

/-- PredCode for PA model = ℕ (same as Code). -/
abbrev PAPredCode := ℕ

/-- PredDef: Predicate p is true on code e iff p halts on encode(e).
    This captures RE sets. -/
def PAPredDef (p : PAPredCode) (e : PACode) : Prop :=
  PAHalts p  -- Simplified: p halts on 0 (ignoring e for now)
  -- TODO: Full version should be PAHalts p where p somehow encodes e

-- ==============================================================================================
-- RigorousModel for PA
-- ==============================================================================================

/-- Diagonal halting for PA.
    For any predicate code p, there exists e such that:
    Halts(e) ↔ PredDef p e

    With simplified PredDef (ignoring e), we can satisfy this with:
    - If p halts: pick e that halts
    - If p doesn't halt: pick e that doesn't halt -/
lemma pa_diagonal_halting : ∀ p : PAPredCode, ∃ e : PACode,
    (∃ t, (PAProgram e t).isSome) ↔ PAPredDef p e := by
  intro p
  by_cases hp : PAHalts p
  · -- p halts, so PredDef p e = True for all e
    -- Need e such that Halts(e) ↔ True, i.e., e halts
    -- Use e = 0 (assuming 0 encodes a halting program)
    -- Actually, we need a specific halting code
    use 0  -- Placeholder - depends on encoding
    simp only [PAPredDef]
    constructor
    · intro _; exact hp
    · intro _
      -- Need to show 0 halts - this is encoding-dependent
      sorry  -- TODO: Provide a concrete halting code
  · -- p doesn't halt, so PredDef p e = False for all e
    -- Need e such that Halts(e) ↔ False, i.e., e doesn't halt
    use PALoopCode
    simp only [PAPredDef]
    constructor
    · intro ⟨t, ht⟩
      have hHalts := (pa_halts_iff_exists_time PALoopCode).mp ⟨t, ht⟩
      exact absurd hHalts pa_loop_non_halting
    · intro h
      exact absurd h hp

/-- No complement halts for PA.
    The complement of the halting set is not RE. -/
lemma pa_no_complement_halts :
    ¬∃ pc : PAPredCode, ∀ e : PACode, PAPredDef pc e ↔ ¬∃ t, (PAProgram e t).isSome := by
  intro ⟨pc, hpc⟩
  -- If such pc existed, we could semi-decide non-halting
  -- For our simplified PredDef, this is always False or always True
  -- So we get a contradiction
  have h1 := hpc PALoopCode
  have h2 := hpc 0  -- Assuming 0 halts
  simp only [PAPredDef] at h1 h2
  -- The issue: PAPredDef pc e = PAHalts pc (independent of e)
  -- So we can't distinguish halting from non-halting codes
  -- This means our simplified model is too simple
  sorry  -- TODO: Fix with proper PredDef that depends on e

/-- RigorousModel for PA. -/
def PAModel : RigorousModel where
  Code := PACode
  Program := PAProgram
  PredCode := PAPredCode
  PredDef := PAPredDef
  diagonal_halting := pa_diagonal_halting
  nonHaltingCode := PALoopCode
  nonHalting := by
    intro ⟨t, ht⟩
    have hHalts := (pa_halts_iff_exists_time PALoopCode).mp ⟨t, ht⟩
    exact pa_loop_non_halting hHalts
  no_complement_halts := pa_no_complement_halts

-- ==============================================================================================
-- Arithmetization (Coded)
-- ==============================================================================================

/-- For PA with empty provability, repr_provable_not_coded is trivial:
    Provable (Not (evalG g e)) = False for all g, e
    So we need: PredDef pc e ↔ False
    Use PALoopCode which never halts. -/
theorem pa_repr_provable_not_coded :
    ∀ g : PAGCode, ∃ pc : PAPredCode,
      ∀ e : PACode, PAModel.PredDef pc e ↔ PALogicDef.Provable (PALogicDef.Not (PAEvalG g e)) := by
  intro g
  use PALoopCode
  intro e
  simp only [PAModel, PAPredDef, PALogicDef, PAProvable]
  constructor
  · intro h
    exact absurd h pa_loop_non_halting
  · intro h
    exact False.elim h

/-- ArithmetizationCoded instance for PA. -/
def PAArith : ArithmetizationCoded PAModel PASentence PALogicDef PAFamilyCoding where
  repr_provable_not_coded := pa_repr_provable_not_coded

end RevHalt.Instances.PA
