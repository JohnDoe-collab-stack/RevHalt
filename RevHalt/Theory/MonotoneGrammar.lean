import RevHalt.Theory.RelativeR1

/-!
# Monotone Grammar: A Natural Grammar Without AdmitsConst

This file explores **strictly increasing sequences** as a natural grammar where:
- `¬AdmitsConst` holds (constants are not strictly increasing)
- `LPO_Eval_R1` has a chance to hold constructively (bounded search)

## Research Question

For `s : ℕ → ℕ` strictly increasing and decidable `P : ℕ → Prop`:
> Is `(∃ n, P(s(n))) ∨ (∀ n, ¬P(s(n)))` constructively decidable?

If yes: LPO_R1 holds for monotone sequences.
If no: We need more structure.

-/

namespace RevHalt.MonotoneGrammar

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Monotone Grammar Definition
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Strictly increasing sequences of natural numbers. -/
def MonoAdm : (ℕ → ℕ) → Prop :=
  fun s => ∀ n, s n < s (n + 1)

/-- Monotone sequences are unbounded. -/
theorem mono_unbounded (s : ℕ → ℕ) (h : MonoAdm s) :
    ∀ k, ∃ n, s n ≥ k := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.zero_le (s 0)⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    use n + 1
    have hlt : s n < s (n + 1) := h n
    omega

/-- Growth bound: s(n) ≥ n for monotone sequences starting at s(0) ≥ 0. -/
theorem mono_growth (s : ℕ → ℕ) (h : MonoAdm s) :
    ∀ n, s n ≥ s 0 + n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : s n < s (n + 1) := h n
    omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) MonoAdm Does NOT Admit Constants
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Constant sequences are NOT strictly increasing. -/
theorem mono_not_const (k : ℕ) : ¬ MonoAdm (fun _ => k) := by
  intro h
  have : k < k := h 0
  omega

/-- Therefore MonoAdm does not admit constants. -/
theorem MonoAdm_not_admits_const :
    ¬ RevHalt.RelativeR1.AdmitsConst (fun s : ℕ → ℕ => MonoAdm s) := by
  intro h
  -- AdmitsConst says: ∀ φ, Adm (fun _ => φ)
  -- For φ = 0, the constant sequence (fun _ => 0) should be in MonoAdm
  have hConst : MonoAdm (fun _ => 0) := h 0
  exact mono_not_const 0 hConst

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) LPO for Bounded Search
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

/-- For monotone sequences, if we're searching for a hit, we only need to search up to
    the preimage of the target. -/
theorem mono_search_bounded (s : ℕ → ℕ) (h : MonoAdm s) (target : ℕ) :
    (∃ n, s n = target) → ∃ n, n ≤ target ∧ s n = target := by
  intro ⟨n, hn⟩
  use n
  constructor
  · -- We need: n ≤ target
    -- From mono_growth: s n ≥ s 0 + n ≥ n
    -- And s n = target, so target ≥ n
    have hGrowth : s n ≥ s 0 + n := mono_growth s h n
    have : s n ≥ n := by omega
    omega
  · exact hn

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Open Question: LPO_R1 for Monotone Sequences
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Key Question

For monotone s and decidable P:
  - Can we decide (∃ n, P(s(n))) ∨ (∀ n, ¬P(s(n)))?

### Partial Answer (Sufficient Condition)

If P is "finitely supported" (true only for finitely many values), then:
- s(n) eventually exceeds all values where P holds
- So we can search up to that bound

### What This Means

For general decidable P, LPO_R1 on MonoAdm requires either:
1. Structure on P (finite support, bounded domain)
2. Structure on s (known growth rate)
3. External principle (markov, LPO)

The grammar alone doesn't give LPO_R1 unconditionally.
-/

/-- Finite support predicate -/
def FiniteSupport (P : ℕ → Prop) : Prop :=
  ∃ bound, ∀ n, n > bound → ¬ P n

/-- Helper: strictly increasing implies larger at larger index -/
theorem mono_lt_of_lt (s : ℕ → ℕ) (hs : MonoAdm s) (m n : ℕ) (h : m < n) :
    s m < s n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases Nat.lt_succ_iff_lt_or_eq.mp h with
    | inl hlt => calc s m < s k := ih hlt
                     _ < s (k + 1) := hs k
    | inr heq => rw [← heq]; exact hs m

/-- LPO_R1 holds for monotone sequences when P has finite support. -/
theorem LPO_R1_mono_finite_support
    (s : ℕ → ℕ) (hs : MonoAdm s)
    (P : ℕ → Prop) [∀ n, Decidable (P n)]
    (hFS : FiniteSupport P) :
    (∃ n, P (s n)) ∨ (∀ n, ¬ P (s n)) := by
  -- Get the bound from finite support
  obtain ⟨bound, hBound⟩ := hFS
  -- s is unbounded, so ∃ N, s(N) > bound
  obtain ⟨N, hN⟩ := mono_unbounded s hs (bound + 1)
  -- Search up to N
  cases existsUpTo (fun i => P (s i)) N with
  | isTrue hEx =>
    left
    exact hEx.elim fun n ⟨_, hPn⟩ => ⟨n, hPn⟩
  | isFalse hNot =>
    right
    intro n
    by_cases hle : n ≤ N
    · exact fun hPsn => hNot ⟨n, hle, hPsn⟩
    · -- n > N, so s(n) > s(N) ≥ bound + 1 > bound
      push_neg at hle
      have hMono : s N < s n := mono_lt_of_lt s hs N n hle
      have hLarge : s n > bound := by omega
      exact hBound (s n) hLarge

end RevHalt.MonotoneGrammar

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.MonotoneGrammar.mono_unbounded
#print axioms RevHalt.MonotoneGrammar.mono_growth
#print axioms RevHalt.MonotoneGrammar.mono_not_const
#print axioms RevHalt.MonotoneGrammar.MonoAdm_not_admits_const
#print axioms RevHalt.MonotoneGrammar.existsUpTo
#print axioms RevHalt.MonotoneGrammar.mono_search_bounded
#print axioms RevHalt.MonotoneGrammar.LPO_R1_mono_finite_support
