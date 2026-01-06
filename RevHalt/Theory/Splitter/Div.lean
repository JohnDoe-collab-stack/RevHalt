import RevHalt.Theory.Splitter.Core
import RevHalt.Theory.Splitter.Auxi

/-!
# RevHalt.Theory.Splitter.Div

Divisibility-based splitter per spec §6.
Split_div(p) splits any info I into two cases:
- I ∧ (p | n)
- I ∧ ¬(p | n)

This is the canonical arithmetic splitter for prime detection.
-/

namespace RevHalt.Splitter.Div

open RevHalt.Splitter
open RevHalt.Splitter.Auxi

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Divisibility Constraints
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Constraint: p divides n. -/
def DivConstraint (p : ℕ) : Constraint ℕ := fun n => p ∣ n

/-- Constraint: p does not divide n. -/
def NotDivConstraint (p : ℕ) : Constraint ℕ := fun n => ¬(p ∣ n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Split_div(p) : The Divisibility Splitter
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Split_div(p) splits I into {I ∧ Div(p), I ∧ NotDiv(p)}.
    Requires p > 0 (for meaningful divisibility). -/
def Split_div (p : ℕ) (_ : p > 0) : Splitter ℕ where
  split I := [I ++ [DivConstraint p], I ++ [NotDivConstraint p]]

  refinement := by
    intro I J hJ n hSatJ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hJ
    cases hJ with
    | inl h =>
      subst h
      intro c hc
      apply hSatJ c
      exact List.mem_append_left _ hc
    | inr h =>
      subst h
      intro c hc
      apply hSatJ c
      exact List.mem_append_left _ hc

  cover := by
    intro I n hSatI
    have hdec : Decidable (p ∣ n) := Nat.decidable_dvd p n
    cases hdec with
    | isTrue hdiv =>
      use I ++ [DivConstraint p]
      constructor
      · simp only [List.mem_cons, List.mem_nil_iff, or_false]; left; trivial
      · intro c hc
        rw [List.mem_append] at hc
        cases hc with
        | inl hInI => exact hSatI c hInI
        | inr hEq =>
          simp only [List.mem_singleton] at hEq
          rw [hEq]
          exact hdiv
    | isFalse hdiv =>
      use I ++ [NotDivConstraint p]
      constructor
      · simp only [List.mem_cons, List.mem_nil_iff, or_false]; right; trivial
      · intro c hc
        rw [List.mem_append] at hc
        cases hc with
        | inl hInI => exact hSatI c hInI
        | inr hEq =>
          simp only [List.mem_singleton] at hEq
          rw [hEq]
          exact hdiv

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Basic Properties
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Split_div always produces exactly 2 cases. -/
theorem split_div_card (p : ℕ) (hp : p > 0) (I : Info ℕ) :
    ((Split_div p hp).split I).length = 2 := by
  simp [Split_div]

/-- Split_div is nontrivial for p > 1. -/
theorem split_div_nontrivial (p : ℕ) (hp : p > 1) :
    isNontrivial ℕ (Split_div p (Nat.lt_trans Nat.zero_lt_one hp)) := by
  intro hTriv
  -- If trivial, then for I = [], both cases should be equivalent to [].
  -- But 0 satisfies DivConstraint p, and 1 does not (since p > 1).
  specialize hTriv [] ([] ++ [DivConstraint p]) (by simp [Split_div])
  have h1 : Sat ℕ [] 1 := fun _ h => by simp at h
  have h1_not_div : ¬ Sat ℕ ([] ++ [DivConstraint p]) 1 := by
    simp only [Sat, List.mem_append, List.mem_singleton, not_forall]
    refine ⟨DivConstraint p, ?_, ?_⟩
    · right; rfl
    · simp only [DivConstraint]
      intro hdvd
      have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
      omega
  have hTriv1 := hTriv 1
  rw [hTriv1] at h1
  exact h1_not_div h1

end RevHalt.Splitter.Div

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks (Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Splitter.Div.DivConstraint
#print axioms RevHalt.Splitter.Div.NotDivConstraint
#print axioms RevHalt.Splitter.Div.Split_div
#print axioms RevHalt.Splitter.Div.split_div_card
#print axioms RevHalt.Splitter.Div.split_div_nontrivial
