/-
  RevHalt.Instances.PA.Encoding

  Halting encoding for PA: HaltEncode + encode_correct.

  ## Key Task

  Define a Σ₁ formula `HaltEncode : M.Code → PropT` that expresses:
    "∃t, evaln(t, e, 0) = some v"

  Then prove:
    `RMHalts M e ↔ Truth (HaltEncode e)`

  This relies on:
  - `evaln_sound` : evaln t c n = some v → eval c n = some v
  - `evaln_complete` : (eval c n).Dom → ∃ t, (evaln t c n).isSome
-/
import RevHalt.Instances.PA.Logic
import Mathlib.Computability.PartrecCode

namespace RevHalt.Instances.PA
open RevHalt_Unified
open Nat.Partrec

-- ==============================================================================================
-- Model: We use ℕ-encoded programs for PA compatibility
-- ==============================================================================================

/-- For PA, we use ℕ as our code type (Gödel numbers).
    This simplifies arithmetic formalization. -/
abbrev PACode := ℕ

/-- Convert ℕ to Partrec.Code -/
def codeOfNat : ℕ → Code := Denumerable.ofNat Code

/-- Halting on input 0 via Partrec. -/
def PAHalts (n : ℕ) : Prop :=
  (Code.eval (codeOfNat n) 0).Dom

-- ==============================================================================================
-- Halting Encoding (E)
-- ==============================================================================================

/-- Encode halting as a PA sentence.
    HaltEncode n is the Σ₁ sentence "program n halts on input 0". -/
def PAHaltEncode (n : PACode) : PASentence :=
  PASentence.Halt n

/-- Encode_correct: RMHalts ↔ Truth(HaltEncode).

    TODO: This requires:
    1. Defining PATruth (PASentence.Halt n) properly
    2. Proving the equivalence via evaln semantics -/
theorem pa_encode_correct : ∀ e : PACode, PAHalts e ↔ PATruth (PAHaltEncode e) := by
  intro e
  -- PAHalts e = (eval (codeOfNat e) 0).Dom
  -- PATruth (Halt e) needs to be defined as this in Logic.lean
  sorry

-- ==============================================================================================
-- Halting Encoding Package
-- ==============================================================================================

-- Halting Encoding Package (to be completed when M is defined)
-- def PAHaltingEncoding : HaltingEncoding M PASentence PALogicDef := ...

end RevHalt.Instances.PA
