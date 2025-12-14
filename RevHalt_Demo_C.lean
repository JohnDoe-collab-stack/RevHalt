import RevHalt.Bridge

namespace RevHalt_Demo_C
open RevHalt

/-!
# RevHalt Demo C: Robustness Model

This instance moves beyond the "False everywhere" logic of Demo B.
- **Predicates**: `PredDef pc e` defined via cases (False, True, Halting). Non-trivial.
- **Provability**: `Provable p := (p = 0)`. Non-empty but sound.
- **Halting**: Still `0` halts, `1` loops.

This tests that the independent code existence proofs hold even when "True but Unprovable"
isn't just a vacuous consequence of empty provability.
-/

-- 1. Toy Types (Concrete Nat)
abbrev ToyCode := ℕ
abbrev ToyPredCode := ℕ
abbrev ToyPropT := ℕ

-- 2. Toy Semantics
-- Code 0 halts immediately. Others loop.
def toyProgram : ToyCode → ℕ → Option ℕ := fun e _ => if e = 0 then some 0 else none

-- Predicates:
-- 0: False
-- 1: True
-- 2: Halting (e = 0)
-- _: False
def toyPredDef : ToyPredCode → ToyCode → Prop
| 0, _ => False
| 1, _ => True
| 2, e => e = 0
| _, _ => False

-- 3. Toy Logic
-- Truth is "Evenness" (p % 2 = 0)
-- Provable is "Is Zero" (p = 0)
def toyTruth    : ToyPropT → Prop := fun p => p % 2 = 0
def toyProvable : ToyPropT → Prop := fun p => p = 0

-- Negation: p -> p + 1
-- If p is even, p+1 is odd (Not True)
-- If p is odd, p+1 is even (Not False)
def toyNot : ToyPropT → ToyPropT := fun p => p + 1

-- False is 1 (Odd)
def toyFalse : ToyPropT := 1

-- Halt Encode: 0 if halts (True/Even), 1 if loops (False/Odd)
def toyHaltEncode : ToyCode → ToyPropT := fun e => if e = 0 then 0 else 1


lemma toy_truth_not_iff : ∀ p, toyTruth (toyNot p) ↔ ¬ toyTruth p := by
  intro p
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;>
    simp [toyTruth, toyNot, Nat.add_mod, hp]

-- Logic Lemmas
lemma toy_soundness : ∀ p, toyProvable p → toyTruth p := by
  intro p hp
  simp [toyProvable, toyTruth] at *
  subst hp
  rfl

lemma toy_consistent : ¬toyProvable toyFalse := by
  simp [toyProvable, toyFalse]

lemma toy_absurd : ∀ p, toyProvable p → toyProvable (toyNot p) → toyProvable toyFalse := by
  intro p hp hnp
  dsimp [toyProvable, toyFalse] at *
  subst hp
  -- but: 1 = 0, and hnp is exactly (0+1=0)
  simp [toyNot] at hnp

-- Model Coherence
lemma toy_diagonal_halting :
  ∀ pc : ToyPredCode, ∃ e : ToyCode, (∃ n, (toyProgram e n).isSome) ↔ toyPredDef pc e := by
  intro pc
  cases pc with
  | zero =>
      refine ⟨1, by simp [toyProgram, toyPredDef]⟩
  | succ pc =>
      cases pc with
      | zero =>
          refine ⟨0, by simp [toyProgram, toyPredDef]⟩
      | succ pc =>
          cases pc with
          | zero =>
              refine ⟨0, by simp [toyProgram, toyPredDef]⟩
          | succ n =>
              refine ⟨1, by simp [toyProgram, toyPredDef]⟩

lemma toy_non_halting : ¬∃ n, (toyProgram 1 n).isSome := by
  simp [toyProgram]

lemma toy_no_complement_halts :
  ¬∃ pc : ToyPredCode, ∀ e, toyPredDef pc e ↔ ¬∃ n, (toyProgram e n).isSome := by
  rintro ⟨pc, hpc⟩
  have h_true_at_1 : toyPredDef pc 1 := by
    have : ¬∃ n, (toyProgram (1 : ToyCode) n).isSome := by simp [toyProgram]
    exact (hpc 1).2 this

  have h_false_at_0 : ¬ toyPredDef pc 0 := by
    intro hPred
    have hNot : ¬∃ n, (toyProgram (0 : ToyCode) n).isSome := (hpc 0).1 hPred
    have hYes : ∃ n, (toyProgram (0 : ToyCode) n).isSome := ⟨0, by simp [toyProgram]⟩
    exact hNot hYes

  cases pc with
  | zero =>
      simp [toyPredDef] at h_true_at_1
  | succ pc =>
      cases pc with
      | zero =>
          have : toyPredDef (1 : ToyPredCode) 0 := by simp [toyPredDef]
          exact h_false_at_0 this
      | succ pc =>
          cases pc with
          | zero =>
              simp [toyPredDef] at h_true_at_1
          | succ n =>
              simp [toyPredDef] at h_true_at_1

-- 4. Construct RigorousModel
def ToyModel : RigorousModel where
  Code := ToyCode
  Program := toyProgram
  PredCode := ToyPredCode
  PredDef := toyPredDef
  diagonal_halting := toy_diagonal_halting
  nonHaltingCode := 1
  nonHalting := toy_non_halting
  no_complement_halts := toy_no_complement_halts

lemma toy_repr_provable_not :
  ∀ G : ToyCode → ToyPropT, ∃ pc : ToyPredCode, ∀ e, toyPredDef pc e ↔ toyProvable (toyNot (G e)) := by
  intro G
  refine ⟨0, ?_⟩
  intro e
  simp [toyPredDef, toyProvable, toyNot]

lemma toy_encode_correct : ∀ e, RMHalts ToyModel e ↔ toyTruth (toyHaltEncode e) := by
  intro e
  simp [toyHaltEncode]
  split
  next h => -- e = 0
    simp_all [RMHalts, ToyModel, toyProgram, toyTruth]
  next h => -- e != 0
    simp_all [RMHalts, ToyModel, toyProgram, toyTruth]

-- 5. Kit Instance
def ToyKit : RHKit where
  Proj := fun X => ∃ n, X n

theorem toy_kit_correct : DetectsMonotone ToyKit := by
  intro X _hMono
  rfl

-- 6. Logic Construction
def ToyLogic : SoundLogicEncoded ToyModel ToyPropT :=
{
  Logic := {
    Provable := toyProvable
    Truth := toyTruth
    soundness := toy_soundness
    Not := toyNot
    FalseP := toyFalse
    consistent := toy_consistent
    absurd := toy_absurd
    truth_not_iff := toy_truth_not_iff
  }
  Arith := {
    repr_provable_not := toy_repr_provable_not
  }
  HaltEncode := toyHaltEncode
  encode_correct := toy_encode_correct
}

-- 7. FINAL DEMONSTRATION
theorem Toy_C_Master_Theorem :
    let ctx := EnrichedContext_from_Encoded ToyModel ToyKit toy_kit_correct ToyLogic
    (∀ e, ctx.RealHalts e ↔ Halts (rmCompile ToyModel e)) ∧
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) ∧
    (∃ T1 : Set ToyPropT, ProvableSet ctx ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p)) := by
  simpa using
    (RevHalt_Master_Complete (PropT := ToyPropT) ToyModel ToyKit toy_kit_correct ToyLogic)

#print Toy_C_Master_Theorem

end RevHalt_Demo_C
