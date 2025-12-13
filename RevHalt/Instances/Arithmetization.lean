/-
  RevHalt Constructive Arithmetization Instance

  Uses Mathlib's `Nat.Partrec.Code` for a fully constructive implementation.
  No `opaque`, no `axiom` in the core definitions.

  ## Status

  **Proven without sorry:**
  - `pr_loop_non_halting` : loopCode never halts
  - `pr_diagonal_halting` : Kleene's fixed point for halting on input 0
  - `pr_no_complement_halts` : complement of halting is not RE (for input 0)

  **Contains sorry (PRModel):**
  - `PRModel.diagonal_halting` : blocked on architectural mismatch
  - `PRModel.no_complement_halts` : blocked on architectural mismatch

  ## Architectural Issue

  There is a **fundamental mismatch** between two halting definitions:

  | Component | Halting Definition |
  |-----------|-------------------|
  | `RigorousModel.diagonal_halting` | `∃ n, (Program e n).isSome` (halts on **some** input) |
  | `pr_diagonal_halting` | `PRHalts e 0` (halts on input **0**) |

  These are not equivalent: a program may halt on input 5 but not on input 0.

  ### Resolution Options

  1. **Modify `RigorousModel`** to use `(Program e 0).isSome` instead of `∃ n, ...`
  2. **Modify `pr_diagonal_halting`** to use `∃ n, PRHalts e n` instead of `PRHalts e 0`
  3. **Accept sorry** in `PRModel` and document it as a known limitation

  The core theorems (`pr_diagonal_halting`, `pr_no_complement_halts`) are correct
  for the "halts on input 0" semantics. The issue is only in connecting them
  to `RigorousModel` which uses "halts on some input" semantics.
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

/-- Program execution: converts Part to Option using classical logic.
    This is noncomputable but gives us a proper Option ℕ interface. -/
noncomputable def PRProgram (c : PRCode) (n : ℕ) : Option ℕ :=
  (Code.eval c n).toOption

/-- Halts if `eval c input` is defined (has a value). -/
def PRHalts (c : PRCode) (input : ℕ) : Prop :=
  (Code.eval c input).Dom

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

/-- The constructive RigorousModel instance.
    Uses ℕ as Code type (Gödel numbers), with PRCode as the underlying representation. -/
noncomputable def PRModel : RigorousModel where
  Code := ℕ  -- Use ℕ directly as Gödel numbers
  Program := fun n k =>
    let c := Denumerable.ofNat PRCode n
    if h : (Code.eval c k).Dom then some (Part.get (Code.eval c k) h) else none
  PredCode := ℕ  -- Predicate codes are also ℕ
  PredDef := fun pc e =>
    -- pc halts on input e means e is in the set defined by pc
    let predCode := Denumerable.ofNat PRCode pc
    PRHalts predCode e
  diagonal_halting := by
    intro pNat
    -- pNat : ℕ is the Gödel number of a predicate code
    let p : PRCode := Denumerable.ofNat PRCode pNat
    -- Use pr_diagonal_halting to get e : PRCode with the diagonal property
    obtain ⟨e, he⟩ := pr_diagonal_halting p
    -- Return encode e as the Gödel number
    use Encodable.encode e
    -- Now prove: (∃ n, Program (encode e) n).isSome ↔ PredDef pNat (encode e)
    constructor
    · -- Forward: halts → predicate holds
      intro ⟨k, hk⟩
      -- hk : Program (encode e) k is some
      -- Program (encode e) k = if (eval (ofNat (encode e)) k).Dom then ...
      have heq : Denumerable.ofNat PRCode (Encodable.encode e) = e := Denumerable.ofNat_encode e
      simp only [heq] at hk
      -- hk : (if h : (Code.eval e k).Dom then some ... else none).isSome
      have hDom : (Code.eval e k).Dom := by
        simp only [Option.isSome_iff_exists] at hk
        obtain ⟨v, hv⟩ := hk
        split_ifs at hv with h
        · exact h
      -- So PRHalts e k is true
      -- But we need PRHalts e 0 for the diagonal
      -- Wait, the statement is: ∃ n, halts on some n
      -- Actually for RigorousModel, it's ∃ n, (Program e n).isSome
      -- Which means e halts on SOME input
      -- But pr_diagonal_halting gives: PRHalts e 0 ↔ PRPredDef p e
      -- We have halts on k, but need halts on 0
      -- This is a mismatch - the RigorousModel uses "halts on some input"
      -- while pr_diagonal_halting uses "halts on input 0"
      -- For now, we use the weaker condition: if halts on 0, then halts on some
      -- Actually the structure of RigorousModel says:
      -- diagonal_halting : ∀ p, ∃ e, (∃ n, (Program e n).isSome) ↔ PredDef p e
      -- So we need: halts-on-any-input ↔ p defines e
      -- This requires a different construction
      sorry
    · -- Backward: predicate holds → halts
      intro hDef
      sorry
  nonHaltingCode := Encodable.encode loopCode
  nonHalting := by
    intro ⟨k, hk⟩
    -- Show encoded loopCode never halts
    -- loopCode is rfind' on const 1, which never halts
    have heq : Denumerable.ofNat PRCode (Encodable.encode loopCode) = loopCode :=
      Denumerable.ofNat_encode loopCode
    simp only [heq] at hk
    -- hk : (if h : (Code.eval loopCode k).Dom then some ... else none).isSome
    -- Need to show False by applying pr_loop_non_halting k
    have hDom : (Code.eval loopCode k).Dom := by
      simp only [Option.isSome_iff_exists] at hk
      obtain ⟨v, hv⟩ := hk
      split_ifs at hv with h
      · exact h
    exact pr_loop_non_halting k hDom
  no_complement_halts := by
    -- The complement of halting is not RE
    intro ⟨pcNat, hpc⟩
    -- pcNat : ℕ, hpc : ∀ e, PredDef pcNat e ↔ ¬∃ n, (Program e n).isSome
    -- PredDef pcNat e = PRHalts (ofNat pcNat) e
    -- So: ∀ e : ℕ, PRHalts (ofNat pcNat) e ↔ ¬∃ n, (Program e n).isSome
    let pc : PRCode := Denumerable.ofNat PRCode pcNat
    -- We need to apply pr_no_complement_halts
    apply pr_no_complement_halts
    use pc
    intro e  -- e : PRCode
    -- Need: PRPredDef pc e ↔ ¬PRHalts e 0
    -- PRPredDef pc e = PRHalts pc (encode e)
    -- From hpc with (encode e): PRHalts pc (encode e) ↔ ¬∃ n, (Program (encode e) n).isSome
    have hspec := hpc (Encodable.encode e)
    -- hspec : PRHalts (ofNat pcNat) (encode e) ↔ ¬∃ n, (Program (encode e) n).isSome
    simp only [pc] at hspec ⊢
    unfold PRPredDef
    -- Goal: PRHalts pc (encode e) ↔ ¬PRHalts e 0
    constructor
    · intro hDef
      -- hDef : PRHalts pc (encode e)
      have hNotHalts := hspec.mp hDef
      -- hNotHalts : ¬∃ n, (Program (encode e) n).isSome
      intro hHalt0
      -- hHalt0 : PRHalts e 0 = (Code.eval e 0).Dom
      -- Program (encode e) 0 = if (eval (ofNat (encode e)) 0).Dom then some ... else none
      apply hNotHalts
      use 0
      have heq : Denumerable.ofNat PRCode (Encodable.encode e) = e := Denumerable.ofNat_encode e
      simp only [heq]
      unfold PRHalts at hHalt0
      simp only [Option.isSome_iff_exists]
      exact ⟨Part.get (Code.eval e 0) hHalt0, by simp [hHalt0]⟩
    · intro hNotHalt0
      -- hNotHalt0 : ¬PRHalts e 0
      apply hspec.mpr
      intro ⟨k, hk⟩
      -- hk : (Program (encode e) k).isSome
      have heq : Denumerable.ofNat PRCode (Encodable.encode e) = e := Denumerable.ofNat_encode e
      simp only [heq] at hk
      have hDom : (Code.eval e k).Dom := by
        simp only [Option.isSome_iff_exists] at hk
        obtain ⟨v, hv⟩ := hk
        split_ifs at hv with h
        · exact h
      -- We have: e halts on k, need to derive contradiction
      -- But hNotHalt0 says e doesn't halt on 0
      -- This doesn't work - halting on k doesn't imply halting on 0!
      -- The issue is the mismatch in halting definitions
      sorry

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
