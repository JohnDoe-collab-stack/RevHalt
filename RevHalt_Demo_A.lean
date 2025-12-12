import RevHalt_Bridge

namespace RevHalt_Demo_A
open RevHalt_Unified

/-!
# RevHalt Demo B: Non-Degenerate Model

This instance has:
- A program that halts (code 0).
- A program that loops (code 1, and all others).
- Truth is `p = 0`.
- Provability is `False` (for now).

This validates that the logic holds even when Halting is non-trivial.
-/

-- 1. Toy Types (Concrete Nat)
abbrev ToyCode := ℕ
abbrev ToyPredCode := ℕ
abbrev ToyPropT := ℕ

-- 2. Toy Semantics
-- Code 0 halts immediately. Others loop.
def toyProgram : ToyCode → ℕ → Option ℕ := fun e _ => if e = 0 then some 0 else none
-- Predicates are empty / False everywhere.
def toyPredDef : ToyPredCode → ToyCode → Prop := fun _ _ => False

-- 3. Toy Logic
-- Truth is p=0. Provability is empty.
def toyProvable : ToyPropT → Prop := fun _ => False
def toyTruth   : ToyPropT → Prop := fun p => p = 0
def toyNot     : ToyPropT → ToyPropT := fun p => if p = 0 then 1 else 0
def toyFalse   : ToyPropT := 1 -- 1 is false because truth is 0

lemma toy_truth_not_iff : ∀ p, toyTruth (toyNot p) ↔ ¬ toyTruth p := by
  intro p
  by_cases h : p = 0
  · subst h; simp [toyTruth, toyNot]
  · simp [toyTruth, toyNot, h]

-- Lemmas for Model Coherence
lemma toy_diagonal_halting : ∀ pc : ToyPredCode, ∃ e : ToyCode, (∃ n, (toyProgram e n).isSome) ↔ toyPredDef pc e := by
  intro pc
  -- PredDef is always False.
  -- We need e such that Halt e <-> False. i.e., ¬Halt e.
  -- Code 1 loops.
  refine ⟨1, ?_⟩
  simp [toyProgram, toyPredDef]

lemma toy_non_halting : ¬∃ n, (toyProgram 1 n).isSome := by
  simp [toyProgram]

lemma toy_no_complement_halts :
  ¬∃ pc : ToyPredCode, ∀ e, toyPredDef pc e ↔ ¬∃ n, (toyProgram e n).isSome := by
  rintro ⟨pc, hpc⟩
  have h_not_halt1 : ¬∃ n, (toyProgram (1 : ToyCode) n).isSome := by
    simp [toyProgram]
  have hFalse : toyPredDef pc (1 : ToyCode) := (hpc 1).2 h_not_halt1
  simpa [toyPredDef] using hFalse

-- 4. Construct RigorousModel with PROOFS (no axioms)
noncomputable def ToyModel : RigorousModel where
  Code := ToyCode
  Program := toyProgram
  PredCode := ToyPredCode
  PredDef := toyPredDef
  diagonal_halting := toy_diagonal_halting
  nonHaltingCode := 1
  nonHalting := toy_non_halting
  no_complement_halts := toy_no_complement_halts

-- 5. Kit Instance
def ToyKit : RHKit where
  Proj := fun X => ∃ n, X n

theorem toy_kit_correct : DetectsMonotone ToyKit := by
  intro X _hMono
  rfl

-- 6. Logic Construction
-- Encode Halting: 0 if halts (Truth), 1 if loops (False).
def toyHaltEncode : ToyCode → ToyPropT := fun e => if e = 0 then 0 else 1

lemma toy_encode_correct : ∀ e, RMHalts ToyModel e ↔ toyTruth (toyHaltEncode e) := by
  intro e
  classical
  by_cases h : e = (0 : ToyCode) <;>
    simp [RMHalts, ToyModel, toyProgram, toyTruth, toyHaltEncode, h]

-- Logic Lemmas
lemma toy_soundness : ∀ p, toyProvable p → toyTruth p := by
  intro p hp
  exact (False.elim hp)

lemma toy_consistent : ¬toyProvable toyFalse := by
  simp [toyProvable]

lemma toy_absurd : ∀ p, toyProvable p → toyProvable (toyNot p) → toyProvable toyFalse := by
  intro p hp hnp
  exact (False.elim hp)

lemma toy_repr_provable_not : ∀ G : ToyModel.Code → ToyPropT, ∃ pc : ToyModel.PredCode, ∀ e, ToyModel.PredDef pc e ↔ toyProvable (toyNot (G e)) := by
  intro G
  refine ⟨(0 : ToyPredCode), ?_⟩
  intro e
  simp [ToyModel, toyPredDef, toyProvable]

noncomputable def ToyLogic : RevHalt_Unified.SoundLogicEncoded ToyModel ToyPropT :=
{
  Provable := toyProvable
  Truth := toyTruth
  soundness := toy_soundness
  Not := toyNot
  FalseP := toyFalse
  consistent := toy_consistent
  absurd := toy_absurd
  truth_not_iff := toy_truth_not_iff
  repr_provable_not := toy_repr_provable_not
  HaltEncode := toyHaltEncode
  encode_correct := toy_encode_correct
}

-- 7. FINAL DEMONSTRATION & SANITY CHECKS
theorem Toy_Master_Theorem :
    let ctx := RevHalt_Unified.EnrichedContext_from_Encoded ToyModel ToyKit toy_kit_correct ToyLogic
    (∀ e, ctx.RealHalts e ↔ Halts (RevHalt_Unified.rmCompile ToyModel e)) ∧
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) ∧
    (∃ T1 : Set ToyPropT, RevHalt_Unified.ProvableSet ctx ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p)) := by
  simpa using
    (RevHalt_Unified.RevHalt_Master_Complete (PropT := ToyPropT) ToyModel ToyKit toy_kit_correct ToyLogic)

-- Check 1: Truth(0) is True. Provable(0) is False.
example : toyTruth 0 ∧ ¬toyProvable 0 := ⟨rfl, id⟩

-- Check 2: Halts(0) is True (Witness provided).
example : RMHalts ToyModel (0 : ToyCode) := by
  refine ⟨0, ?_⟩
  simp [ToyModel, toyProgram]

-- Check 3: Halts(1) is False.
example : ¬RMHalts ToyModel (1 : ToyCode) := by
  intro h
  rcases h with ⟨n, hn⟩
  simp [ToyModel, toyProgram] at hn


#print Toy_Master_Theorem

end RevHalt_Demo_A
