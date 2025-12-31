import RevHalt.Base.Trace
import RevHalt.Theory.Categorical
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Basic

/-!
# RevHalt.Theory.CollatzBoundary

Collatz packaged as a RevHalt-style trace problem:
- finite stages are constructive (for this decidable trace)
- the ω-stage is exactly the "LPO-shaped" jump (for decidable traces)
- uniformization (choosing a bound function) isolates `Classical.choice`
-/

namespace RevHalt

/-- Consolidated (as in OrdinalMechanical.lean) -/
abbrev HaltsUpTo (T : Trace) (m : ℕ) : Prop := ∃ n ≤ m, T n

/-- Consolidated (as in OrdinalMechanical.lean) -/
abbrev StabilizesUpTo (T : Trace) (m : ℕ) : Prop := ∀ n ≤ m, ¬ T n

/-- Generic finite-stage dichotomy for decidable traces (0 axiom). -/
theorem haltsUpTo_or_stabilizesUpTo (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    HaltsUpTo T m ∨ StabilizesUpTo T m := by
  induction m with
  | zero =>
      by_cases h0 : T 0
      · left; exact ⟨0, Nat.le_refl 0, h0⟩
      · right
        intro n hn
        have : n = 0 := Nat.le_zero.mp hn
        subst this
        exact h0
  | succ m ih =>
      cases ih with
      | inl hH =>
          left
          rcases hH with ⟨k, hk, hTk⟩
          exact ⟨k, Nat.le_trans hk (Nat.le_succ m), hTk⟩
      | inr hS =>
          by_cases hlast : T (m + 1)
          · left; exact ⟨m + 1, Nat.le_refl (m + 1), hlast⟩
          · right
            intro k hk
            have hk' : k ≤ m ∨ k = m + 1 := by
              cases Nat.lt_or_eq_of_le hk with
              | inl hlt =>
                  left
                  exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hlt)
              | inr heq =>
                  right; exact heq
            cases hk' with
            | inl hkm => exact hS k hkm
            | inr heq =>
                subst heq
                exact hlast

section CollatzTrace

-- A "step function" (Collatz can be plugged in later).
variable (step : ℕ → ℕ)

/-- Iteration of `step`. -/
def iter : ℕ → ℕ → ℕ
  | n, 0     => n
  | n, k + 1 => step (iter n k)

/-- The trace "hits 1 at time k". (Decidable because equality on ℕ.) -/
def hits1 (n : ℕ) : Trace := fun k => iter step n k = 1

instance (n : ℕ) : ∀ k, Decidable (hits1 step n k) := by
  intro k
  dsimp [hits1]
  infer_instance

/-- Finite stage set: "n hits 1 within m steps". -/
def Stage (m : ℕ) : Set ℕ := { n | HaltsUpTo (hits1 step n) m }

/-- ω-stage set: "n hits 1 at some time". -/
def Stageω : Set ℕ := { n | Halts (hits1 step n) }

theorem Stage_mono : ∀ {m m' : ℕ}, m ≤ m' → Stage step m ⊆ Stage step m' := by
  intro m m' hmm n hn
  rcases hn with ⟨k, hk, hk1⟩
  exact ⟨k, Nat.le_trans hk hmm, hk1⟩

theorem mem_Stage_iff (m n : ℕ) :
    n ∈ Stage step m ↔ (∃ k ≤ m, iter step n k = 1) := Iff.rfl

theorem mem_Stageω_iff (n : ℕ) :
    n ∈ Stageω step ↔ (∃ k, iter step n k = 1) := Iff.rfl

/-- Finite-stage dichotomy specialized to the Collatz-style trace (0 axiom). -/
theorem finite_stage_dichotomy (n m : ℕ) :
    HaltsUpTo (hits1 step n) m ∨ StabilizesUpTo (hits1 step n) m :=
  haltsUpTo_or_stabilizesUpTo (T := hits1 step n) m

/-- Stabilizes definition local to this file. -/
def StabilizesLocal (T : Trace) : Prop := ∀ n, ¬ T n

/-- Kernel-style negative side for this trace. -/
theorem Stabilizes_hits1_iff (n : ℕ) :
    StabilizesLocal (hits1 step n) ↔ (∀ k, iter step n k ≠ 1) := by
  rfl

/-- Same statement but as a "kernel equation" via `up_eq_bot_iff`. -/
theorem up_hits1_eq_bot_iff (n : ℕ) :
    up (hits1 step n) = ⊥ ↔ (∀ k, iter step n k ≠ 1) := by
  -- `up_eq_bot_iff` in RevHalt/Theory/Categorical.lean: `up T = ⊥ ↔ ∀ n, ¬ T n`
  simpa [hits1, iter] using (up_eq_bot_iff (T := hits1 step n))

/-!
## Uniformization boundary (isolates `Classical.choice`)
-/

def CollatzTerminates : Prop := ∀ n, ∃ k, iter step n k = 1
def UniformCollatz : Prop := ∃ f : ℕ → ℕ, ∀ n, iter step n (f n) = 1

theorem UniformCollatz_implies (h : UniformCollatz step) : CollatzTerminates step := by
  rcases h with ⟨f, hf⟩
  intro n
  exact ⟨f n, hf n⟩

theorem CollatzTerminates_to_UniformCollatz (h : CollatzTerminates step) : UniformCollatz step := by
  classical
  refine ⟨fun n => Classical.choose (h n), ?_⟩
  intro n
  exact Classical.choose_spec (h n)

end CollatzTrace

end RevHalt

-- Axiom audit (Classical.choice should only appear in CollatzTerminates_to_UniformCollatz):
#print axioms RevHalt.haltsUpTo_or_stabilizesUpTo
#print axioms RevHalt.finite_stage_dichotomy
#print axioms RevHalt.up_hits1_eq_bot_iff
#print axioms RevHalt.CollatzTerminates_to_UniformCollatz
