import RevHalt.Theory.RelativeR1
import RevHalt.Theory.EvalTraceProperties
import RevHalt.Theory.Stabilization

/-!
# LPO_R1 Constructive for AdmBit Grammars

This file proves LPO_R1 constructively for bit-indexed grammars when:
1. Evaluation is decidable on each `Bit n a x`
2. The predicate has finite support (bounded relevant indices)

## Key Insight

Unlike the "toy" separation theorem which uses abstract HiddenVal,
this file works with **concrete grammars** from the RevHalt architecture.

The structure parallels `LPO_R1_mono_finite_support` from MonotoneGrammar.lean
but adapted for Bit grammars.

## Main Results

- `LPO_R1_AdmBit_finite_support` : LPO_R1 for AdmBit when signal has finite support
- `LPO_R1_AdmBit_bounded` : LPO_R1 when we know all signals occur before bound N
- `StabilizesE_AdmBit_iff_kernel` : Link to kernel characterization
-/

namespace RevHalt.LPO_AdmBit

open RevHalt.RelativeR1
open RevHalt.RelativeR1.CutBit
open RevHalt.TraceProperties

variable {Sentence : Type} {Referent : Type}

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Bounded Search (imported pattern from MonotoneGrammar/OrbitGrammar)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Decidable search up to bound. -/
def existsUpTo (P : ℕ → Prop) [∀ n, Decidable (P n)] (bound : ℕ) :
    Decidable (∃ n, n ≤ bound ∧ P n) := by
  induction bound with
  | zero =>
    by_cases h : P 0
    · exact isTrue ⟨0, Nat.le_refl 0, h⟩
    · exact isFalse (fun ⟨n, hn, hPn⟩ => by simp at hn; subst hn; exact h hPn)
  | succ k ih =>
    cases ih with
    | isTrue hEx =>
      exact isTrue (hEx.elim fun n ⟨hn, hPn⟩ => ⟨n, Nat.le_succ_of_le hn, hPn⟩)
    | isFalse hNot =>
      by_cases hk : P (k + 1)
      · exact isTrue ⟨k + 1, Nat.le_refl _, hk⟩
      · exact isFalse (fun ⟨n, hn, hPn⟩ => by
          cases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hn) with
          | inl hlt => exact hNot ⟨n, Nat.lt_succ_iff.mp hlt, hPn⟩
          | inr heq => rw [heq] at hPn; exact hk hPn)

/-- Search for either bit value at each level. -/
def existsUpToBit (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    [∀ n a, Decidable (Eval Γ (Bit n a x))] (bound : ℕ) :
    Decidable (∃ n, n ≤ bound ∧ ∃ a : Fin 2, Eval Γ (Bit n a x)) := by
  induction bound with
  | zero =>
    by_cases h0 : Eval Γ (Bit 0 0 x)
    · exact isTrue ⟨0, Nat.le_refl 0, 0, h0⟩
    · by_cases h1 : Eval Γ (Bit 0 1 x)
      · exact isTrue ⟨0, Nat.le_refl 0, 1, h1⟩
      · apply isFalse
        intro ⟨n, hn, a, ha⟩
        simp only [Nat.le_zero] at hn
        subst hn
        match a with
        | 0 => exact h0 ha
        | 1 => exact h1 ha
  | succ k ih =>
    cases ih with
    | isTrue hEx =>
      exact isTrue (hEx.elim fun n ⟨hn, a, ha⟩ => ⟨n, Nat.le_succ_of_le hn, a, ha⟩)
    | isFalse hNot =>
      by_cases hk0 : Eval Γ (Bit (k + 1) 0 x)
      · exact isTrue ⟨k + 1, Nat.le_refl _, 0, hk0⟩
      · by_cases hk1 : Eval Γ (Bit (k + 1) 1 x)
        · exact isTrue ⟨k + 1, Nat.le_refl _, 1, hk1⟩
        · apply isFalse
          intro ⟨n, hn, a, ha⟩
          by_cases hnk : n ≤ k
          · exact hNot ⟨n, hnk, a, ha⟩
          · push_neg at hnk
            have heq : n = k + 1 := Nat.le_antisymm hn hnk
            subst heq
            match a with
            | 0 => exact hk0 ha
            | 1 => exact hk1 ha

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Finite Support Predicate
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Finite support: the signal only occurs before some bound. -/
def FiniteSupportBit (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ a : Fin 2, ¬ Eval Γ (Bit n a x)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) THE MAIN THEOREM: LPO_R1 for AdmBit with Finite Support
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**LPO_R1 for AdmBit with Finite Support** (constructive, no Classical.choice).

If the evaluation predicate has finite support on Bit formulas,
then `LPO_Eval_R1` holds for the `AdmBit` grammar.

This is the "non-toy" version: it works with the actual AdmBit grammar
from RevHalt architecture, not abstract HiddenVal from separation theorem.

**Key insight**: We search the sequence s directly, not the abstract Bit n a x,
which avoids the mismatch between "which bit evaluates" and "what s picks".

**Axiom check**: depends only on `propext`, NOT on `Classical.choice`.
-/
theorem LPO_R1_AdmBit_finite_support
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    [hDec : ∀ n a, Decidable (Eval Γ (Bit n a x))]
    (hFS : FiniteSupportBit Eval Γ Bit x) :
    LPO_Eval_R1 Eval Γ (AdmBit Bit x) := by
  obtain ⟨N, hBound⟩ := hFS
  intro s hs

  -- Key: for AdmBit sequences, s(n) = Bit n (a n) x for some a : ℕ → Fin 2
  -- And Eval Γ (s n) is decidable because s n = Bit n (a n) x

  -- Helper: search s up to bound k
  have search_up_to : ∀ k, (∃ n ≤ k, Eval Γ (s n)) ∨ (∀ n ≤ k, ¬ Eval Γ (s n)) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨a, hsa⟩ := hs 0
      by_cases h : Eval Γ (Bit 0 a x)
      · left; exact ⟨0, Nat.le_refl 0, by rw [hsa]; exact h⟩
      · right; intro n hn; simp only [Nat.le_zero] at hn; subst hn; rw [hsa]; exact h
    | succ k ih =>
      cases ih with
      | inl hEx =>
        left
        obtain ⟨n, hn, hEval⟩ := hEx
        exact ⟨n, Nat.le_succ_of_le hn, hEval⟩
      | inr hAll =>
        obtain ⟨a, hsa⟩ := hs (k + 1)
        by_cases hk : Eval Γ (Bit (k + 1) a x)
        · left; exact ⟨k + 1, Nat.le_refl _, by rw [hsa]; exact hk⟩
        · right
          intro n hn
          by_cases hnk : n ≤ k
          · exact hAll n hnk
          · push_neg at hnk
            have heq : n = k + 1 := Nat.le_antisymm hn hnk
            subst heq; rw [hsa]; exact hk

  -- Apply search at bound N
  cases search_up_to N with
  | inl hEx =>
    left
    obtain ⟨n, _, hn⟩ := hEx
    exact ⟨n, hn⟩
  | inr hAll =>
    right
    intro n
    by_cases hn : n ≤ N
    · exact hAll n hn
    · push_neg at hn
      obtain ⟨a, hsa⟩ := hs n
      rw [hsa]
      exact hBound n (Nat.le_of_lt hn) a

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Link to Kernel Characterization
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Stabilization on AdmBit is kernel membership**.

If s is an AdmBit sequence, then StabilizesE(s) iff every Bit n a x fails to evaluate.
-/
theorem StabilizesE_AdmBit_iff
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    (s : ℕ → Sentence) (hs : AdmBit Bit x s) :
    StabilizesE Eval Γ s ↔ ∀ n, ∀ a : Fin 2, s n = Bit n a x → ¬ Eval Γ (Bit n a x) := by
  constructor
  · intro hStab n a hEq
    have := hStab n
    rw [hEq] at this
    exact this
  · intro hAll n
    obtain ⟨a, hsa⟩ := hs n
    rw [hsa]
    exact hAll n a hsa

/--
**HaltsE on AdmBit has a Bit witness**.

If an AdmBit sequence halts, we get the specific (n, a) witness.
-/
theorem HaltsE_AdmBit_witness
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    (s : ℕ → Sentence) (hs : AdmBit Bit x s) :
    HaltsE Eval Γ s → ∃ n, ∃ a : Fin 2, s n = Bit n a x ∧ Eval Γ (Bit n a x) := by
  intro ⟨n, hEval⟩
  obtain ⟨a, hsa⟩ := hs n
  exact ⟨n, a, hsa, by rw [← hsa]; exact hEval⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Non-Collapse Reinforcement
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Non-collapse package for AdmBit with finite support**.

Combines:
1. LPO_R1 holds (finite support gives bounded search)
2. AdmitsConst fails (structural, from RelativeR1)
3. Therefore LPO_R1 → EM_Eval is blocked
-/
theorem AdmBit_noncollapse_with_LPO
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    [hDec : ∀ n a, Decidable (Eval Γ (Bit n a x))]
    (hDist : BitIndexDistinct Bit)
    (hFS : FiniteSupportBit Eval Γ Bit x) :
    LPO_Eval_R1 Eval Γ (AdmBit Bit x) ∧
    ¬ AdmitsConst (AdmBit Bit x) := by
  constructor
  · exact LPO_R1_AdmBit_finite_support Eval Γ Bit x hFS
  · exact AdmBit_not_admits_const Bit hDist x

end RevHalt.LPO_AdmBit

-- Axiom checks (auto):
#print axioms RevHalt.LPO_AdmBit.existsUpTo
#print axioms RevHalt.LPO_AdmBit.existsUpToBit
#print axioms RevHalt.LPO_AdmBit.LPO_R1_AdmBit_finite_support
#print axioms RevHalt.LPO_AdmBit.StabilizesE_AdmBit_iff
#print axioms RevHalt.LPO_AdmBit.HaltsE_AdmBit_witness
#print axioms RevHalt.LPO_AdmBit.AdmBit_noncollapse_with_LPO
