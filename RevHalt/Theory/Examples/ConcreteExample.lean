import RevHalt.Theory.Hierarchy
import RevHalt.Theory.Splitter.Core
import RevHalt.Theory.Stabilization

/-!
# Concrete Example: Modular Rotation (2n mod 5)

This file demonstrates the **full RevHalt framework** on a concrete dynamical system:
- **System**: `Next(n) = (2 * n) mod 5` on {1, 2, 3, 4}, with 0 as absorbing state
- **Target**: reaching 0 (the "bad" state)
- **Start**: 1

The orbit from 1 is: `1 → 2 → 4 → 3 → 1 → ...` (period 4, never hits 0).

We prove `Stabilizes T` directly, showing the trace never halts.
-/

namespace RevHalt.Examples.ModularRotation

open RevHalt.Splitter

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) The Dynamical System
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Position type: natural numbers. -/
abbrev Pos := ℕ

/-- The dynamics: multiplication by 2 mod 5. 0 is absorbing. -/
def Next (n : Pos) : Pos :=
  if n = 0 then 0
  else (2 * n) % 5

/-- The target predicate: hitting 0 is "bad". -/
def Target (n : Pos) : Prop := n = 0

/-- The starting position. -/
def start : Pos := 1

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Orbit Definition
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Iterate Next t times from start. -/
def orbit : ℕ → Pos
  | 0 => start
  | t + 1 => Next (orbit t)

-- Verify orbit values by computation
example : orbit 0 = 1 := rfl
example : orbit 1 = 2 := rfl
example : orbit 2 = 4 := rfl
example : orbit 3 = 3 := rfl
example : orbit 4 = 1 := rfl  -- Period!

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Invariant: orbit values are in {1, 2, 3, 4}
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Predicate: n is in the safe set {1, 2, 3, 4}. -/
def InSafe (n : ℕ) : Prop := n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/-- Next preserves InSafe. -/
theorem Next_preserves_safe (n : ℕ) (hn : InSafe n) : InSafe (Next n) := by
  rcases hn with rfl | rfl | rfl | rfl
  · -- n = 1: Next 1 = 2
    unfold Next; simp; right; left; rfl
  · -- n = 2: Next 2 = 4
    unfold Next; simp; right; right; right; rfl
  · -- n = 3: Next 3 = 6 % 5 = 1
    unfold Next; simp; left; rfl
  · -- n = 4: Next 4 = 8 % 5 = 3
    unfold Next; simp; right; right; left; rfl

/-- Start is in the safe set. -/
theorem start_safe : InSafe start := by
  unfold start InSafe; left; rfl

/-- The orbit stays safe forever. -/
theorem orbit_safe (t : ℕ) : InSafe (orbit t) := by
  induction t with
  | zero => exact start_safe
  | succ t ih => exact Next_preserves_safe (orbit t) ih

/-- Safe values are non-zero. -/
theorem safe_ne_zero (n : ℕ) (hn : InSafe n) : n ≠ 0 := by
  rcases hn with rfl | rfl | rfl | rfl <;> omega

/-- The orbit never hits zero. -/
theorem orbit_never_zero (t : ℕ) : orbit t ≠ 0 :=
  safe_ne_zero (orbit t) (orbit_safe t)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) The Trace and Stabilization
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The trace: T(t) = true iff orbit(t) = 0. -/
def T : RevHalt.Trace := fun t => Target (orbit t)

/--
**Main Theorem**: The trace stabilizes (never halts).

This demonstrates the full RevHalt framework application:
- We have a non-trivial dynamical system (multiplication mod prime)
- The orbit could in principle hit 0
- But starting from 1, it cycles in {1,2,3,4} forever
- Therefore: `Stabilizes T` (the Π₁ property)
-/
theorem example_stabilizes : RevHalt.Stabilizes T := by
  intro t
  simp only [T, Target]
  exact orbit_never_zero t

/-- Corollary: The trace never halts. -/
theorem example_not_halts : ¬ RevHalt.Halts T := by
  rw [← RevHalt.Stabilizes_iff_NotHalts]
  exact example_stabilizes

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Axiom Audit
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms InSafe
#print axioms Next_preserves_safe
#print axioms orbit_safe
#print axioms orbit_never_zero
#print axioms example_stabilizes
#print axioms example_not_halts

/-!
## Summary

We have demonstrated:
1. A concrete dynamical system: `Next(n) = 2n mod 5`
2. An invariant predicate: `InSafe n := n ∈ {1, 2, 3, 4}`
3. Next preserves InSafe: `Next_preserves_safe`
4. Orbits stay safe: `orbit_safe`
5. Safe implies non-zero: `safe_ne_zero`
6. The key theorem: `example_stabilizes : Stabilizes T`

This is a **complete, axiom-minimal proof** of non-halting for a specific system.
-/

end RevHalt.Examples.ModularRotation
