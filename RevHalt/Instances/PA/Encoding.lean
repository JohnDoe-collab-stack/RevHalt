/-
  RevHalt.Instances.PA.Encoding

  Halting encoding for PA: HaltEncode + encode_correct.

  ## Key Design

  - PACode := ℕ (Gödel numbers)
  - Uses Denumerable.ofNat to convert ℕ to Partrec.Code
  - PAHaltEncode wraps a code in PASentence.Halt
  - encode_correct connects RMHalts to PATruth
-/
import RevHalt.Instances.PA.Logic
import RevHalt.Unified.Coded.Interface

namespace RevHalt.Instances.PA
open RevHalt_Unified
open RevHalt_Unified.Coded
open Nat.Partrec

-- ==============================================================================================
-- Model: ℕ-encoded programs for PA compatibility
-- ==============================================================================================

/-- For PA, we use ℕ as our code type (Gödel numbers).
    This simplifies arithmetic formalization. -/
abbrev PACode := ℕ

/-- Convert ℕ to Partrec.Code. -/
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

    This works because:
    - RMHalts M e = haltsOnZero e (for our model)
    - PATruth (Halt e) = haltsOnZero e (by definition in Logic.lean) -/
theorem pa_encode_correct_raw : ∀ e : PACode, PAHalts e ↔ PATruth (PAHaltEncode e) := by
  intro e
  -- PAHalts e = (Code.eval (codeOfNat e) 0).Dom
  -- PATruth (Halt e) = haltsOnZero e = (Code.eval (codeOfNat e) 0).Dom
  rfl

-- ==============================================================================================
-- RigorousModel for PA (using ℕ codes)
-- ==============================================================================================

/-- Time-bounded execution using evaln. -/
def PAProgram (n : PACode) (t : ℕ) : Option ℕ :=
  Code.evaln t (codeOfNat n) 0

/-- Halts iff exists time bound. -/
lemma pa_halts_iff_exists_time (n : PACode) :
    (∃ t, (PAProgram n t).isSome) ↔ PAHalts n := by
  simp only [PAProgram, PAHalts, codeOfNat]
  constructor
  · intro ⟨t, ht⟩
    simp only [Option.isSome_iff_exists] at ht
    obtain ⟨x, hx⟩ := ht
    have := Code.evaln_sound hx
    exact Part.dom_iff_mem.mpr ⟨x, this⟩
  · intro hDom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hDom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩

/-- A code that never halts (loop). -/
def PALoopCode : PACode := Encodable.encode (Code.rfind' (Code.const 1))

/-- PALoopCode never halts. -/
lemma pa_loop_non_halting : ¬PAHalts PALoopCode := by
  unfold PAHalts PALoopCode codeOfNat
  simp only [Denumerable.ofNat_encode]
  -- rfind' (const 1) searches for first input returning 0, but const 1 always returns 1
  intro h
  simp only [Code.eval] at h
  simp only [Nat.unpaired] at h
  have hmap := Part.dom_iff_mem.mp h
  obtain ⟨v, hv⟩ := hmap
  simp only [Part.map_eq_map, Part.mem_map_iff] at hv
  obtain ⟨m, hm, _⟩ := hv
  simp only [Code.eval_const, Part.map_some] at hm
  rw [Nat.mem_rfind] at hm
  have h1 := hm.1
  rw [Part.mem_some_iff] at h1
  simp at h1

end RevHalt.Instances.PA
