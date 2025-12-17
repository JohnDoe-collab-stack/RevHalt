import RevHalt.Base.Trace
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Dynamics.Instances.CollatzTrace

**Concrete computational trace for the Collatz problem.**

## Objective

This file provides the missing piece: a **concrete, computable** definition of the
Collatz problem as a `Trace` in the RevHalt sense.

## Key Definitions

1. `collatzStep' n` : One step of the Collatz iteration (fixed at 1)
2. `collatzIter'' n t` : The value after t iterations starting from n
3. `collatzTrace' n` : The trace that becomes true when the sequence reaches 1
4. `CollatzHolds' n` : The proposition "n eventually reaches 1"

## Main Results

1. `CollatzHolds'_iff_halts` : `CollatzHolds' n ↔ Halts (collatzTrace' n)`
2. Decidability of `collatzTrace'`
3. Verified small cases (n = 1 to 7)

## Philosophy

The Collatz conjecture states: `∀ n > 0, CollatzHolds' n`

If true, the question becomes: is it **provable** in PA/ZFC?
- If provable → not in Gap
- If true but unprovable → in Gap (Gödelian)
-/

namespace RevHalt.Dynamics.Instances.CollatzTrace

open RevHalt

-- ============================================================================
-- 1) The Collatz Function (Computable)
-- ============================================================================

/-- Modified Collatz step that fixes 1 (standard stopping condition). -/
def collatzStep' (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

/-- The Collatz iteration: apply collatzStep' t times starting from n. -/
def collatzIter'' (n : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => collatzStep' (collatzIter'' n t)

-- ============================================================================
-- 2) Collatz as a Trace
-- ============================================================================

/-- The Collatz trace for starting value n: true at time t iff value is 1. -/
def collatzTrace' (n : ℕ) : Trace :=
  fun t => collatzIter'' n t = 1

/-- Decidability: we can compute whether collatzTrace' n t holds. -/
instance collatzTrace'_decidable (n t : ℕ) : Decidable (collatzTrace' n t) :=
  inferInstanceAs (Decidable (collatzIter'' n t = 1))

/-- The proposition "n eventually reaches 1 under Collatz iteration". -/
def CollatzHolds' (n : ℕ) : Prop := ∃ t : ℕ, collatzIter'' n t = 1

/-- CollatzHolds' is equivalent to Halts of the trace. -/
theorem CollatzHolds'_iff_halts (n : ℕ) : CollatzHolds' n ↔ Halts (collatzTrace' n) := by
  rfl

-- ============================================================================
-- 3) Basic Properties of Collatz Iteration
-- ============================================================================

/-- Starting from 1, we stay at 1. -/
theorem collatzIter''_one : ∀ t, collatzIter'' 1 t = 1 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [collatzIter'', ih, collatzStep']
    simp

/-- 1 satisfies Collatz. -/
theorem collatzHolds'_one : CollatzHolds' 1 := ⟨0, rfl⟩

/-- collatzStep' is idempotent at 1. -/
theorem collatzStep'_one : collatzStep' 1 = 1 := by
  simp [collatzStep']

/-- Once we reach 1, we stay at 1. -/
theorem collatzIter''_of_one (n t : ℕ) (h : collatzIter'' n t = 1) :
    ∀ s ≥ t, collatzIter'' n s = 1 := by
  intro s hs
  have key : ∀ k, collatzIter'' n (t + k) = 1 := by
    intro k
    induction k with
    | zero => exact h
    | succ k ihk =>
      show collatzStep' (collatzIter'' n (t + k)) = 1
      rw [ihk, collatzStep'_one]
  have : s = t + (s - t) := by omega
  rw [this]
  exact key (s - t)

-- ============================================================================
-- 4) Monotonicity: Once halted, stays halted
-- ============================================================================

/-- The Collatz trace is monotone once it becomes true. -/
theorem collatzTrace'_mono (n : ℕ) : ∀ t₁ t₂, t₁ ≤ t₂ → collatzTrace' n t₁ → collatzTrace' n t₂ := by
  intro t₁ t₂ h12 ht1
  exact collatzIter''_of_one n t₁ ht1 t₂ h12

-- ============================================================================
-- 5) Verified Small Cases
-- ============================================================================

/-- Collatz holds for 2: 2 → 1. -/
theorem collatzHolds'_2 : CollatzHolds' 2 := ⟨1, by native_decide⟩

/-- Collatz holds for 3: 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1. -/
theorem collatzHolds'_3 : CollatzHolds' 3 := ⟨7, by native_decide⟩

/-- Collatz holds for 4: 4 → 2 → 1. -/
theorem collatzHolds'_4 : CollatzHolds' 4 := ⟨2, by native_decide⟩

/-- Collatz holds for 5: 5 → 16 → 8 → 4 → 2 → 1. -/
theorem collatzHolds'_5 : CollatzHolds' 5 := ⟨5, by native_decide⟩

/-- Collatz holds for 6: 6 → 3 → ... → 1. -/
theorem collatzHolds'_6 : CollatzHolds' 6 := ⟨8, by native_decide⟩

/-- Collatz holds for 7. -/
theorem collatzHolds'_7 : CollatzHolds' 7 := ⟨16, by native_decide⟩

-- ============================================================================
-- 6) The Resolution Strategy (Documentation)
-- ============================================================================

/-!
## Strategy for "Resolving" Collatz via RevHalt

The framework suggests this path:

### Step 1: Define the encoding
```
def CollatzProp (n : ℕ) : PropT := encode "CollatzHolds' n"
```

### Step 2: Establish the bridge
```
theorem collatz_bridge (n : ℕ) :
    Truth (CollatzProp n) ↔ Halts (collatzTrace' n) := ...
```

### Step 3: Gap analysis
If we could show:
```
theorem collatz_in_gap (n : ℕ) (hTrue : CollatzHolds' n) :
    CollatzProp n ∈ Gap ctx := ...
```

This would prove: "Collatz is true but unprovable" for that n.

### The Hard Part
The hard part is step 3. To show C(n) ∈ Gap, we need:
1. C(n) is TRUE (requires knowing Collatz holds for n)
2. C(n) is NOT PROVABLE (requires meta-theoretic argument)

(2) is the Gödelian part. We would need to show that PA/ZFC cannot prove
CollatzHolds' n for some specific n, even though it's true.

### Alternative: Use Conway's result
Conway showed that generalized Collatz functions can encode any Turing machine.
If we formalize this:
1. Encode a halting-undecidable TM as a generalized Collatz function
2. Show the trace is in Gap

This would give us a Collatz-like function in Gap, even if not THE Collatz function.
-/

end RevHalt.Dynamics.Instances.CollatzTrace
