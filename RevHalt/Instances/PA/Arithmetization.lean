/-
  RevHalt.Instances.PA.Arithmetization

  Coded Arithmetization for PA.

  ## Key Structure

  Uses `FamilyCoding` to represent computable formula families:
  - `GCode := ℕ` (codes for primitive recursive functions on formulas)
  - `evalG g e` = decode(F_g(e)) where F_g is the g-th PR function

  ## Main Theorem

  `repr_provable_not_coded`:
    ∀ g : GCode, ∃ pc : PredCode,
      ∀ e, PredDef pc e ↔ Provable (Not (evalG g e))

  This is provable because:
  1. PA's proof predicate is RE (semi-decidable)
  2. Composition of PR functions is PR
  3. RE predicates are definable via PredDef
-/
import RevHalt.Instances.PA.Logic
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

/-- Placeholder: Evaluate a coded formula family.
    TODO: Implement via Gödel numbering of formulas. -/
def PAEvalG : PAGCode → ℕ → PASentence := sorry

/-- FamilyCoding instance for PA. -/
def PAFamilyCoding : FamilyCoding ℕ PASentence where
  GCode := PAGCode
  evalG := PAEvalG

-- ==============================================================================================
-- Arithmetization (Coded)
-- ==============================================================================================

/-- For PA, we can prove repr_provable_not_coded because:
    1. PAProvable is RE (there exists a proof π that PA-proves σ)
    2. The predicate "∃π, ProofCheck(π, encode(Not(evalG g e)))" is RE
    3. RE predicates are PredDef-definable in our model

    TODO: Full proof requires formalizing PA's proof checker. -/
theorem pa_repr_provable_not_coded (M : RigorousModel) :
    ∀ g : PAGCode, ∃ pc : M.PredCode,
      ∀ e : M.Code, M.PredDef pc e ↔ PALogicDef.Provable (PALogicDef.Not (PAEvalG g sorry)) := by
  intro g
  -- The key insight:
  -- PAProvable (Not (evalG g e)) = ∃π, ProofCheck(π, ⌜¬φ_g(e)⌝)
  -- This is an RE predicate in e
  -- Therefore, there exists a PredCode that semi-decides it
  sorry

end RevHalt.Instances.PA
