/-
  RevHalt Arithmetization Instance via Mathlib

  Based on Mathlib's `Nat.Partrec.Code` and `evaln`.
  No `opaque`, no `axiom` in the core definitions.
  Uses classical logic (open Classical, noncomputable) for Part/Option conversion.

  ## Status: ✅ COMPLETE - No sorry!

  **All theorems proven:**
  - `pr_loop_non_halting` : loopCode never halts
  - `pr_diagonal_halting` : Kleene's fixed point for halting on input 0
  - `pr_no_complement_halts` : complement of halting is not RE
  - `halts0_iff_exists_time` : bridges time semantics with halting semantics
  - `PRModel` : complete RigorousModel instance

  ## Key Insight: Time vs Input Semantics

  The `RigorousModel.Program e n` interprets `n` as a **time/step budget**.
  We use `Code.evaln t c 0` where:
  - `t` = time budget (the variable index)
  - `0` = input (fixed)

  This gives: `∃ t, (Program e t).isSome` ↔ "halts on input 0 in finite time"

  ## Code Encoding

  We identify codes with ℕ via `Denumerable.ofNat` / `Encodable.encode`.
  The round-trip property `Denumerable.ofNat_encode` ensures consistency.
-/
import RevHalt.Unified
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting

namespace RevHalt.Instances.Arithmetization

open RevHalt_Unified
open Nat.Partrec
open Classical

-- ==============================================================================================
-- 1. Constructive Computability Model using Mathlib
-- ==============================================================================================

/-- Code type is Mathlib's partial recursive code. -/
abbrev PRCode := Code

/-- Halts if `eval c input` is defined (has a value). -/
def PRHalts (c : PRCode) (input : ℕ) : Prop :=
  (Code.eval c input).Dom

/-- Time-bounded program execution on input 0.
    Uses Mathlib's `evaln` which provides a computable approximation.
    `t` is the time budget, input is fixed to 0. -/
def PRProgram_time (c : PRCode) (t : ℕ) : Option ℕ :=
  Code.evaln t c 0

/-- Key lemma: existence of a time bound ↔ halts on input 0.
    This bridges the RigorousModel's `∃ n, (Program e n).isSome` with `PRHalts e 0`. -/
lemma halts0_iff_exists_time (c : PRCode) :
    (∃ t, (PRProgram_time c t).isSome) ↔ PRHalts c 0 := by
  simp only [PRProgram_time, PRHalts]
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

/-- The key insight: Mathlib's `Code.eval` is the universal partial function.
    This is constructive in the sense that `evaln` provides the approximation. -/

-- ==============================================================================================
-- 2. Building RigorousModel from Mathlib
-- ==============================================================================================


-- For `PredCode`, we use the same `Code` type.
-- `PredDef p e` means `e` is in the domain of `eval p` (i.e., `p` halts on `e`).
-- This captures RE sets: W_p = { e | p halts on e }.

abbrev PRPredCode := PRCode

def PRPredDef (p : PRPredCode) (e : PRCode) : Prop :=
  PRHalts p (Encodable.encode e)

/--
  **Diagonal Halting (Kleene's fixed point theorem)**:
  For any definable predicate `p`, there exists a code `e` such that:
  `Halts(e) ↔ PredDef p e`

  This follows from Mathlib's `fixed_point₂` theorem (Kleene's second recursion theorem).
  The construction: for any p, we build e such that
  eval e 0 terminates iff p halts on (encode e).
-/
theorem pr_diagonal_halting : ∀ p : PRPredCode, ∃ e, PRHalts e 0 ↔ PRPredDef p e := by
  intro p
  -- Strategy: Use fixed_point₂ to construct e such that
  -- eval e n = g e n, where g e 0 = eval p (encode e)
  -- Then: PRHalts e 0 ↔ (eval e 0).Dom ↔ (eval p (encode e)).Dom ↔ PRPredDef p e

  -- Define g : Code → ℕ →. ℕ as g c n := eval p (encode c)
  -- We need this to be Partrec₂
  have hg : Partrec₂ (fun (c : PRCode) (n : ℕ) => Code.eval p (Encodable.encode c)) := by
    exact Code.eval_part.comp (Computable.const p) (Computable.encode.comp Computable.fst)

  -- By fixed_point₂: ∃ c, eval c = g c = fun n => eval p (encode c)
  obtain ⟨e, he⟩ := Code.fixed_point₂ hg
  use e

  -- Now prove the equivalence
  constructor
  · -- PRHalts e 0 → PRPredDef p e
    intro hHalt
    unfold PRHalts at hHalt
    unfold PRPredDef PRHalts
    -- hHalt : (Code.eval e 0).Dom
    -- Goal: (Code.eval p (encode e)).Dom
    -- By he: eval e = fun n => eval p (encode e)
    -- So eval e 0 = eval p (encode e)
    have heq : Code.eval e 0 = Code.eval p (Encodable.encode e) := by
      have := congr_fun he 0
      simp only at this
      exact this
    rw [← heq]
    exact hHalt
  · -- PRPredDef p e → PRHalts e 0
    intro hDef
    unfold PRPredDef PRHalts at hDef
    unfold PRHalts
    -- hDef : (Code.eval p (encode e)).Dom
    -- Goal: (Code.eval e 0).Dom
    have heq : Code.eval e 0 = Code.eval p (Encodable.encode e) := by
      have := congr_fun he 0
      simp only at this
      exact this
    rw [heq]
    exact hDef

/-- A code that never halts. -/
def loopCode : PRCode := Code.rfind' (Code.const 1)
-- rfind' on a function that always returns 1 (never 0) loops forever.

/-- loopCode never halts on any input. -/
theorem pr_loop_non_halting : ∀ n, ¬PRHalts loopCode n := by
  intro n
  unfold PRHalts loopCode
  -- rfind' (const 1) searches for the first input that returns 0
  -- But const 1 always returns 1, so it never terminates
  simp only [Code.eval]
  -- Now have: ¬(Nat.unpaired (fun a m => (Nat.rfind ...).map ...) n).Dom
  intro h
  -- Unfold the Part definition to get at the rfind
  simp only [Nat.unpaired] at h
  -- The map preserves domains, so we need rfind to have domain
  have hmap := Part.dom_iff_mem.mp h
  obtain ⟨v, hv⟩ := hmap
  simp only [Part.map_eq_map, Part.mem_map_iff] at hv
  obtain ⟨m, hm, _⟩ := hv
  -- hm : m ∈ Nat.rfind (fun k => (fun m => m = 0) <$> Code.eval (Code.const 1) ...)
  -- Nat.rfind returns m when the predicate first becomes true at m
  -- But Code.eval (const 1) always returns Part.some 1, so predicate is always false
  simp only [Code.eval_const, Part.map_some] at hm
  -- hm : m ∈ Nat.rfind (fun _ => Part.some (decide (1 = 0)))
  -- Nat.rfind p returns n when p n = Part.some true for the first time
  -- But decide (1 = 0) = false always, so this can never happen
  -- Use Nat.mem_rfind to extract the specification
  rw [Nat.mem_rfind] at hm
  -- hm.1 says: true ∈ Part.some (decide (1 = 0))
  -- Part.mem_some_iff: a ∈ Part.some b ↔ a = b
  have h1 := hm.1
  rw [Part.mem_some_iff] at h1
  -- h1 : true = decide (1 = 0)
  -- But decide (1 = 0) = false (since 1 ≠ 0), so true = false, contradiction
  simp at h1

/--
  **No Complement Halting**: The complement of the halting set is not RE.
  This follows from Mathlib's `halting_problem_not_re` theorem.
-/
theorem pr_no_complement_halts :
    ¬∃ pc : PRPredCode, ∀ e : PRCode, PRPredDef pc e ↔ ¬PRHalts e 0 := by
  intro ⟨pc, hpc⟩
  -- halting_problem_not_re : ¬REPred (fun c => ¬(eval c 0).Dom)
  have hNotRE := ComputablePred.halting_problem_not_re 0
  apply hNotRE
  -- Need to show: REPred (fun c => ¬(eval c 0).Dom)
  -- Key insight: PRPredDef pc e ↔ PRHalts pc (encode e) ↔ (eval pc (encode e)).Dom
  -- And by hpc: PRPredDef pc e ↔ ¬PRHalts e 0 ↔ ¬(eval e 0).Dom
  -- So pc halting on (encode c) iff c doesn't halt on 0
  -- This makes the complement RE via pc
  unfold REPred
  -- We need: Partrec (fun c => Part.assert (¬(eval c 0).Dom) (fun _ => Part.some ()))
  -- This is equivalent to: Partrec (fun c => if ¬(eval c 0).Dom then Part.some () else Part.none)
  -- Since PRPredDef pc c ↔ ¬PRHalts c 0, and PRPredDef pc c = PRHalts pc (encode c),
  -- we have: (eval pc (encode c)).Dom ↔ ¬(eval c 0).Dom
  -- The domain of eval pc (encode c) witnesses ¬(eval c 0).Dom
  have hPartrec : Partrec (fun (c : PRCode) => (Code.eval pc (Encodable.encode c)).map (fun _ => ())) := by
    exact (Nat.Partrec.Code.eval_part.comp (Computable.const pc) Computable.encode).map
      (Computable.const ()).to₂
  refine Partrec.of_eq hPartrec ?_
  intro c
  ext u
  constructor
  · -- From map to assert
    intro hMem
    simp only [Part.mem_map_iff] at hMem
    obtain ⟨v, hv, _⟩ := hMem
    have hDom : (Code.eval pc (Encodable.encode c)).Dom := Part.dom_iff_mem.mpr ⟨v, hv⟩
    have hDef : PRPredDef pc c := by unfold PRPredDef PRHalts; exact hDom
    have hNotHalt : ¬PRHalts c 0 := (hpc c).mp hDef
    simp only [Part.mem_assert_iff, Part.mem_some_iff]
    unfold PRHalts at hNotHalt
    exact ⟨hNotHalt, trivial⟩
  · -- From assert to map
    intro hAssert
    simp only [Part.mem_assert_iff, Part.mem_some_iff] at hAssert
    obtain ⟨hNotDom, _⟩ := hAssert
    have hNotHalt : ¬PRHalts c 0 := by unfold PRHalts; exact hNotDom
    have hDef : PRPredDef pc c := (hpc c).mpr hNotHalt
    unfold PRPredDef PRHalts at hDef
    simp only [Part.mem_map_iff]
    exact ⟨Part.get (Code.eval pc (Encodable.encode c)) hDef, Part.get_mem hDef, trivial⟩

/-- The RigorousModel instance using Mathlib's Partrec.Code directly.

    **No Denumerable conversion needed** - Code = PRCode directly.
    **Program is computable** - uses only evaln (not Part.toOption).

    Semantics: Program c t = evaln t c 0
    - `t` = time budget
    - `0` = input (fixed)

    So: `∃ t, (Program c t).isSome` ↔ "c halts on input 0 in finite time" -/
def PRModel : RigorousModel where
  Code := PRCode
  Program := fun c t => Code.evaln t c 0
  PredCode := PRCode
  PredDef := fun p e => PRHalts p (Encodable.encode e)
  diagonal_halting := by
    intro p
    obtain ⟨e, he⟩ := pr_diagonal_halting p
    use e
    -- Goal: (∃ t, (evaln t e 0).isSome) ↔ PredDef p e
    -- PredDef p e = PRHalts p (encode e) = PRPredDef p e
    -- he : PRHalts e 0 ↔ PRPredDef p e
    constructor
    · intro ⟨t, ht⟩
      have hHalt : PRHalts e 0 := (halts0_iff_exists_time e).mp ⟨t, ht⟩
      have hPredDef : PRPredDef p e := he.mp hHalt
      unfold PRPredDef at hPredDef
      exact hPredDef
    · intro hDef
      have hPredDef : PRPredDef p e := hDef
      have hHalt : PRHalts e 0 := he.mpr hPredDef
      obtain ⟨t, ht⟩ := (halts0_iff_exists_time e).mpr hHalt
      exact ⟨t, ht⟩
  nonHaltingCode := loopCode
  nonHalting := by
    intro ⟨t, ht⟩
    have hHalt : PRHalts loopCode 0 := (halts0_iff_exists_time loopCode).mp ⟨t, ht⟩
    exact pr_loop_non_halting 0 hHalt
  no_complement_halts := by
    intro ⟨pc, hpc⟩
    apply pr_no_complement_halts
    use pc
    intro e
    -- Goal: PRPredDef pc e ↔ ¬PRHalts e 0
    -- hpc e : PRHalts pc (encode e) ↔ ¬∃ t, (evaln t e 0).isSome
    have hspec := hpc e
    unfold PRPredDef
    constructor
    · intro hDef
      have hNotExists := hspec.mp hDef
      intro hHalt
      have ⟨t, ht⟩ := (halts0_iff_exists_time e).mpr hHalt
      exact hNotExists ⟨t, ht⟩
    · intro hNotHalt
      apply hspec.mpr
      intro ⟨t, ht⟩
      have hHalt := (halts0_iff_exists_time e).mp ⟨t, ht⟩
      exact hNotHalt hHalt

-- ==============================================================================================
-- 3. Logic (same as before, but we could also use Mathlib's logic)
-- ==============================================================================================

-- For simplicity, we keep the abstract logic structure.
-- A fully constructive logic would require defining a proof system.

inductive ArithSentence
| Halt (c : PRCode) (n : ℕ) : ArithSentence  -- "Code c halts on input n"
| Not (s : ArithSentence) : ArithSentence
| And (s1 s2 : ArithSentence) : ArithSentence
| TrueS : ArithSentence
| FalseS : ArithSentence

def ArithTruth : ArithSentence → Prop
| ArithSentence.Halt c n => PRHalts c n
| ArithSentence.Not s => ¬ArithTruth s
| ArithSentence.And s1 s2 => ArithTruth s1 ∧ ArithTruth s2
| ArithSentence.TrueS => True
| ArithSentence.FalseS => False

/--
  Provable in a sound, consistent theory.
  We postulate soundness and consistency as properties of the theory.
  A fully constructive version would define a proof term type.
-/
def ArithProvable (T : Set ArithSentence) (s : ArithSentence) : Prop :=
  s ∈ T

-- For interface compliance, we package this.
variable (T : Set ArithSentence)
variable (hT_sound : ∀ s ∈ T, ArithTruth s)
variable (hT_consistent : ArithSentence.FalseS ∉ T)

-- ==============================================================================================
-- 4. Full Instantiation (sketch)
-- ==============================================================================================

-- The remaining work is connecting PRModel to the framework interfaces.
-- This requires proving the Arithmetization bridge using Mathlib's theorems.

end RevHalt.Instances.Arithmetization
