import RevHalt.Theory.Hierarchy
import RevHalt.Theory.Splitter.Core
import RevHalt.Theory.Stabilization

/-!
# Infinite State Splitter Example

This file demonstrates the RevHalt framework on an **infinite state space**.

## System
- **State space**: ℕ (infinite!)
- **Dynamics**: Residue rotation mod 5
- **Target**: `n % 5 = 0`
- **Start**: Any n with safe residue

## Key insight
Infinite state space, but residue class determines everything.
-/

namespace RevHalt.Examples.InfiniteState

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) The Infinite Dynamical System
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Position type: all natural numbers (infinite). -/
abbrev Pos := ℕ

/-- Dynamics: rotate residue by multiplication by 2 mod 5. -/
def Next (n : Pos) : Pos :=
  let r := n % 5
  let q := n / 5
  if r = 0 then n else 5 * q + (2 * r) % 5

/-- Target: hitting residue 0. -/
def Target (n : Pos) : Prop := n % 5 = 0

/-- Iterate Next t times. -/
def orbit (start : Pos) : ℕ → Pos
  | 0 => start
  | t + 1 => Next (orbit start t)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Residue Preservation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- (5*q + r) % 5 = r % 5. -/
theorem mod5_add_mul5 (q r : ℕ) : (5 * q + r) % 5 = r % 5 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

/-- Next residue transformation. -/
theorem Next_residue (n : Pos) (hr : n % 5 ≠ 0) :
    Next n % 5 = (2 * (n % 5)) % 5 := by
  simp only [Next]
  -- Use hr to simplify the if
  have h_cond : (n % 5 = 0) = False := by exact eq_false_of_ne hr
  rw [h_cond]
  simp only [if_false]
  -- Now term is (5 * (n/5) + (2*(n%5))%5) % 5
  rw [mod5_add_mul5]
  exact Nat.mod_mod _ _

/-- Safe residue predicate: 1, 2, 3, or 4. -/
def SafeResidue (n : ℕ) : Prop := n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4

/-- The residue cycle maps safe to safe. -/
theorem residue_cycle_safe (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) :
    (2 * r) % 5 = 1 ∨ (2 * r) % 5 = 2 ∨ (2 * r) % 5 = 3 ∨ (2 * r) % 5 = 4 := by
  rcases hr with rfl | rfl | rfl | rfl
  · right; left; rfl
  · right; right; right; rfl
  · left; rfl
  · right; right; left; rfl

/-- SafeResidue implies non-zero residue. -/
theorem safe_nonzero (n : ℕ) (hn : SafeResidue n) : n % 5 ≠ 0 := by
  unfold SafeResidue at hn
  rcases hn with h | h | h | h <;> rw [h] <;> simp

/-- Next preserves SafeResidue. -/
theorem Next_preserves_safe (n : Pos) (hn : SafeResidue n) : SafeResidue (Next n) := by
  have hr : n % 5 ≠ 0 := safe_nonzero n hn
  rw [SafeResidue]
  rw [Next_residue n hr]
  unfold SafeResidue at hn
  exact residue_cycle_safe (n % 5) hn

/-- Orbit preserves SafeResidue. -/
theorem orbit_safe (start : Pos) (hstart : SafeResidue start) (t : ℕ) :
    SafeResidue (orbit start t) := by
  induction t with
  | zero => exact hstart
  | succ t ih => exact Next_preserves_safe (orbit start t) ih

/-- SafeResidue implies not Target. -/
theorem safe_not_target (n : ℕ) (hn : SafeResidue n) : ¬ Target n := by
  unfold SafeResidue Target at *
  rcases hn with h | h | h | h <;> rw [h] <;> simp

/-- Orbit never hits target. -/
theorem orbit_avoids_target (start : Pos) (hstart : SafeResidue start) (t : ℕ) :
    ¬ Target (orbit start t) :=
  safe_not_target (orbit start t) (orbit_safe start hstart t)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Concrete Starting Points and Stabilization
-- ═══════════════════════════════════════════════════════════════════════════════

def start1 : Pos := 1
def start6 : Pos := 6
def start1001 : Pos := 1001

theorem start1_safe : SafeResidue start1 := by unfold SafeResidue start1; left; rfl
theorem start6_safe : SafeResidue start6 := by unfold SafeResidue start6; left; rfl
theorem start1001_safe : SafeResidue start1001 := by unfold SafeResidue start1001; left; rfl

/-- The trace from start1. -/
def T1 : RevHalt.Trace := fun t => Target (orbit start1 t)

/-- Main theorem: T1 stabilizes. -/
theorem infinite_stabilizes_1 : RevHalt.Stabilizes T1 := by
  intro t
  exact orbit_avoids_target start1 start1_safe t

/-- General theorem: ANY start with SafeResidue gives stabilization. -/
theorem infinite_stabilizes_general (n : Pos) (hn : SafeResidue n) :
    RevHalt.Stabilizes (fun t => Target (orbit n t)) := by
  intro t
  exact orbit_avoids_target n hn t

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Axiom Audit
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms Next_preserves_safe
#print axioms orbit_safe
#print axioms orbit_avoids_target
#print axioms infinite_stabilizes_1
#print axioms infinite_stabilizes_general

end RevHalt.Examples.InfiniteState
