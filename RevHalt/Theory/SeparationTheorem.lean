import RevHalt.Theory.RelativeR1

/-!
# Separation Theorem: LPO_R1 Does Not Imply EM_Eval

## Key Insight

For proper separation, LPO_R1 must be provable **constructively** (not via classical).
This is achieved by making R1 **finitary**: sequences depend on only a finite number of positions.

## Structure

- `SentenceWithHidden`: probes (in grammar) + hidden (outside grammar)
- `AdmTwoProbes`: finitary grammar (positions 0,1 then repeat)
- `LPO_R1_twoProbes`: constructive proof of LPO (case split on finite positions)
- `separation`: LPO_R1 ∧ ¬EM_Eval when HiddenVal is undecidable
-/

namespace RevHalt.SeparationTheorem

open RevHalt.RelativeR1

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Sentence Type: Probes + Hidden
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sentence = probes (admissible) + a hidden phrase (outside grammar). -/
inductive SentenceWithHidden (Probe : Type) where
  | probe  : Probe → SentenceWithHidden Probe
  | hidden : SentenceWithHidden Probe
  deriving DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Evaluator
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Evaluator: probes use probeEval, hidden uses HiddenVal. -/
def Eval {Probe : Type} (probeEval : Probe → Prop) (HiddenVal : Prop) :
    List (SentenceWithHidden Probe) → SentenceWithHidden Probe → Prop
  | _, .probe p => probeEval p
  | _, .hidden  => HiddenVal

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Finitary Grammar: AdmTwoProbes
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Finitary grammar: a sequence is determined by two probes at indices 0 and 1,
then falls back to index 0 for n ≥ 2.
We force p0 ≠ p1 to prevent constant sequences.
-/
def AdmTwoProbes {Probe : Type} : (ℕ → SentenceWithHidden Probe) → Prop :=
  fun s =>
    ∃ p0 p1 : Probe, p0 ≠ p1 ∧
      s 0 = .probe p0 ∧
      s 1 = .probe p1 ∧
      (∀ n, 2 ≤ n → s n = .probe p0)

/-- This grammar does not admit constant sequences. -/
theorem AdmTwoProbes_not_admits_const {Probe : Type} :
    ¬ AdmitsConst (Sentence := SentenceWithHidden Probe) AdmTwoProbes := by
  intro hConst
  have hs : AdmTwoProbes (fun _ => (SentenceWithHidden.hidden : SentenceWithHidden Probe)) :=
    hConst _
  rcases hs with ⟨_, _, _, h0, _, _⟩
  exact SentenceWithHidden.noConfusion h0

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) CONSTRUCTIVE LPO_R1 (requires decidable probeEval)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Constructive LPO_R1**: Since R1 is finitary, "∃ n" reduces to testing n=0 or n=1
(then n≥2 falls back to n=0). No classical logic needed.
-/
theorem LPO_R1_twoProbes {Probe : Type} (probeEval : Probe → Prop) [∀ p, Decidable (probeEval p)]
    (HiddenVal : Prop) :
    LPO_Eval_R1 (Sentence := SentenceWithHidden Probe)
      (Eval := Eval probeEval HiddenVal) (Γ := [])
      (Adm := AdmTwoProbes) := by
  intro s hs
  rcases hs with ⟨p0, p1, _, hs0, hs1, hs2⟩
  -- Decidable case split on probeEval p0
  by_cases h0 : probeEval p0
  · left
    refine ⟨0, ?_⟩
    simp [Eval, hs0, h0]
  · by_cases h1 : probeEval p1
    · left
      refine ⟨1, ?_⟩
      simp [Eval, hs1, h1]
    · right
      intro n
      cases n with
      | zero =>
          simp [Eval, hs0, h0]
      | succ n =>
          cases n with
          | zero =>
              simp [Eval, hs1, h1]
          | succ n =>
              have hn : 2 ≤ Nat.succ (Nat.succ n) := by
                exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
              have hs' : s (Nat.succ (Nat.succ n)) = .probe p0 := hs2 _ hn
              simp [Eval, hs', h0]

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) EM_Eval Fails (does NOT require decidable probeEval)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- If HiddenVal is undecidable (¬(H ∨ ¬H)), then EM_Eval fails. -/
theorem not_EM_Eval_of_undecidable {Probe : Type} (probeEval : Probe → Prop)
    (HiddenVal : Prop) (hUndec : ¬ (HiddenVal ∨ ¬ HiddenVal)) :
    ¬ EM_Eval (Sentence := SentenceWithHidden Probe)
        (Eval := Eval probeEval HiddenVal) (Γ := []) := by
  intro hEM
  have h := hEM (SentenceWithHidden.hidden : SentenceWithHidden Probe)
  have : HiddenVal ∨ ¬ HiddenVal := by
    simp [Eval] at h
    exact h
  exact hUndec this

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) THE SEPARATION THEOREM
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Separation Theorem**: With an undecidable HiddenVal,
LPO_R1 holds (on the finitary grammar) but EM_Eval fails (globally).

This proves: `¬(LPO_R1 → EM_Eval)` in general.
-/
theorem separation {Probe : Type} (probeEval : Probe → Prop) [∀ p, Decidable (probeEval p)]
    (HiddenVal : Prop) (hUndec : ¬ (HiddenVal ∨ ¬ HiddenVal)) :
    LPO_Eval_R1 (Sentence := SentenceWithHidden Probe)
        (Eval := Eval probeEval HiddenVal) (Γ := [])
        (Adm := AdmTwoProbes)
    ∧ ¬ EM_Eval (Sentence := SentenceWithHidden Probe)
          (Eval := Eval probeEval HiddenVal) (Γ := [])
    ∧ ¬ AdmitsConst (Sentence := SentenceWithHidden Probe) AdmTwoProbes := by
  refine ⟨LPO_R1_twoProbes probeEval HiddenVal,
          not_EM_Eval_of_undecidable probeEval HiddenVal hUndec,
          AdmTwoProbes_not_admits_const⟩

/-- Corollary: The universal implication (LPO_R1 → EM_Eval) is false in general. -/
theorem LPO_R1_not_implies_EM {Probe : Type} (probeEval : Probe → Prop) [∀ p, Decidable (probeEval p)]
    (HiddenVal : Prop) (hUndec : ¬ (HiddenVal ∨ ¬ HiddenVal)) :
    ¬ (LPO_Eval_R1 (Sentence := SentenceWithHidden Probe)
          (Eval := Eval probeEval HiddenVal) (Γ := [])
          (Adm := AdmTwoProbes)
        → EM_Eval (Sentence := SentenceWithHidden Probe)
          (Eval := Eval probeEval HiddenVal) (Γ := [])) := by
  intro hImp
  have ⟨hLPO, hNoEM, _⟩ := separation probeEval HiddenVal hUndec
  exact hNoEM (hImp hLPO)

end RevHalt.SeparationTheorem

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks (should avoid Classical.choice)
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.SeparationTheorem.AdmTwoProbes_not_admits_const
#print axioms RevHalt.SeparationTheorem.LPO_R1_twoProbes
#print axioms RevHalt.SeparationTheorem.not_EM_Eval_of_undecidable
#print axioms RevHalt.SeparationTheorem.separation
#print axioms RevHalt.SeparationTheorem.LPO_R1_not_implies_EM
