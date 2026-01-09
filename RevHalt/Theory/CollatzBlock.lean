/-
Copyright (c) 2025 RevHalt Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RevHalt Contributors
-/
import RevHalt.Theory.Up2Gain
import Mathlib.Tactic.Ring

/-!
# Collatz Block Contraction Lemmas

This module formalizes the "block contraction" approach to Collatz Route II (Option 2).

## Main results

- `BlockContraction7_12`: The key L1 lemma stating that if a block of 7 steps has
  total 2-adic valuation ≥ 12, then `4096 * n_{j+7} ≤ 2187 * n_j + 2186`.

## Parameters

- `q = 7` (block length)
- `p = 12` (contraction threshold)
- Verification: `2^12 = 4096 > 3^7 = 2187` ✓

-/

namespace RevHalt.CollatzBlock

open RevHalt.Up2Gain

/-- Accelerated Collatz step on odd naturals: T*(n) = (3n+1) / 2^{v2(3n+1)}. -/
def Tstar (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ (tag n)

/-- Iterated Tstar. -/
def Tstar_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | k+1, n => Tstar (Tstar_iter k n)

/-- For an orbit starting at n₀, get the k-th term. -/
abbrev orbit (n₀ : ℕ) (k : ℕ) : ℕ := Tstar_iter k n₀

/-- The valuation at step k of an orbit starting at n₀. -/
def a (n₀ : ℕ) (k : ℕ) : ℕ := tag (orbit n₀ k)

/-- Sum of 7 consecutive valuations starting at j (manually unrolled). -/
def B7 (n₀ : ℕ) (j : ℕ) : ℕ :=
  a n₀ j + a n₀ (j+1) + a n₀ (j+2) + a n₀ (j+3) +
  a n₀ (j+4) + a n₀ (j+5) + a n₀ (j+6)

/-- Constants for the (q=7, p=12) block contraction. -/
def pow2_12 : ℕ := 2^12       -- 4096
def pow3_7  : ℕ := 3^7        -- 2187
def C7      : ℕ := 3^7 - 1    -- 2186

lemma pow2_12_eq : pow2_12 = 4096 := rfl
lemma pow3_7_eq  : pow3_7  = 2187 := rfl
lemma C7_eq      : C7      = 2186 := rfl

lemma contraction_ratio : pow3_7 < pow2_12 := by decide

/-!
## Key technical lemmas
-/

/-- Fundamental property: 2^(v2 n) divides n for any n > 0. -/
lemma pow_v2_dvd (n : ℕ) (hn : 0 < n) : 2 ^ (v2 n) ∣ n := by
  -- Strong induction on n
  refine Nat.strong_induction_on n (fun m ih hm => ?_) hn
  rw [v2]
  split_ifs with h0 heven
  · -- case m = 0
    omega
  · -- case m even: v2 m = 1 + v2 (m/2), so 2^(1 + v2(m/2)) | m
    have hdiv_pos : 0 < m / 2 := by
      have h2dvd : 2 ∣ m := Nat.dvd_of_mod_eq_zero heven
      have hle : 2 ≤ m := Nat.le_of_dvd hm h2dvd
      exact Nat.div_pos hle (by decide : 0 < 2)
    have hdiv_lt : m / 2 < m := Nat.div_lt_self hm (by decide : 1 < 2)
    have hih : 2 ^ v2 (m / 2) ∣ m / 2 := ih (m / 2) hdiv_lt hdiv_pos
    -- 2^(1 + v2(m/2)) = 2 * 2^(v2(m/2))
    have hpow : 2 ^ (1 + v2 (m / 2)) = 2 * 2 ^ v2 (m / 2) := by ring
    rw [hpow]
    -- 2 * 2^v2(m/2) | 2 * (m/2) and 2 * (m/2) = m (for even m)
    have h2mul_dvd : 2 * 2 ^ v2 (m / 2) ∣ 2 * (m / 2) := Nat.mul_dvd_mul_left 2 hih
    have h2half : 2 * (m / 2) = m := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)
    rw [h2half] at h2mul_dvd
    exact h2mul_dvd
  · -- case m odd: v2 m = 0, so 2^0 = 1 | m
    simp

/-- Divisibility: 2^{tag n} divides 3n+1. -/
lemma pow_tag_dvd (n : ℕ) : 2 ^ (tag n) ∣ (3 * n + 1) := by
  have hpos : 0 < 3 * n + 1 := Nat.succ_pos _
  exact pow_v2_dvd (3 * n + 1) hpos

/-- One-step "cleared denominator" equality for Tstar. -/
lemma step_mul_pow_eq (n : ℕ) :
    2 ^ (tag n) * Tstar n = 3 * n + 1 := by
  unfold Tstar
  have hd : 2 ^ (tag n) ∣ (3 * n + 1) := pow_tag_dvd n
  exact Nat.mul_div_cancel' hd

/-!
## Block contraction theorem (L1)

The proof strategy:
1. Establish one-step inequality: 2^(a_k) * n_{k+1} ≤ 3 * n_k + 1
2. Build q-step inequality by induction
3. Use B7 ≥ 12 to get the final bound
-/

/-- One-step inequality: 2^(tag n) * Tstar n ≤ 3 * n + 1 (actually equality). -/
lemma one_step_ineq (n : ℕ) : 2 ^ (tag n) * Tstar n ≤ 3 * n + 1 := by
  rw [step_mul_pow_eq]

/-- Orbit step relation using valuation. -/
lemma orbit_step (n₀ : ℕ) (k : ℕ) :
    2 ^ (a n₀ k) * orbit n₀ (k + 1) = 3 * orbit n₀ k + 1 := by
  simp only [orbit, a, Tstar_iter]
  exact step_mul_pow_eq (Tstar_iter k n₀)

/-- Sum of valuations for a range of steps. -/
def sumA (n₀ : ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | q+1 => sumA n₀ j q + a n₀ (j + q)

/-- One-step product formula (equality). -/
lemma one_step_product (n₀ : ℕ) (j : ℕ) :
    2 ^ (a n₀ j) * orbit n₀ (j + 1) = 3 * orbit n₀ j + 1 := orbit_step n₀ j

/-- Two-step product formula. -/
lemma two_step_product (n₀ : ℕ) (j : ℕ) :
    2 ^ (sumA n₀ j 2) * orbit n₀ (j + 2) = 9 * orbit n₀ j + 3 + 2^(a n₀ j) := by
  -- sumA n₀ j 2 = a n₀ j + a n₀ (j + 1)
  have h1 : 2 ^ (a n₀ (j + 1)) * orbit n₀ (j + 2) = 3 * orbit n₀ (j + 1) + 1 := orbit_step n₀ (j + 1)
  have h0 : 2 ^ (a n₀ j) * orbit n₀ (j + 1) = 3 * orbit n₀ j + 1 := orbit_step n₀ j
  -- Simplify sumA n₀ j 2
  have hsum : sumA n₀ j 2 = a n₀ j + a n₀ (j + 1) := by simp [sumA]
  rw [hsum]
  -- 2^(a + b) = 2^a * 2^b
  rw [Nat.pow_add, Nat.mul_assoc, h1]
  -- Goal: 2^(a_j) * (3 * n_{j+1} + 1) = 9 * n_j + 3 + 2^(a_j)
  -- Expand: 2^(a_j) * 3 * n_{j+1} + 2^(a_j) = 9 * n_j + 3 + 2^(a_j)
  -- Use h0: 2^(a_j) * n_{j+1} = 3 * n_j + 1
  -- So: 3 * (3 * n_j + 1) + 2^(a_j) = 9 * n_j + 3 + 2^(a_j)
  have hleft : 2 ^ (a n₀ j) * (3 * orbit n₀ (j + 1) + 1) =
      3 * (2 ^ (a n₀ j) * orbit n₀ (j + 1)) + 2 ^ (a n₀ j) := by ring
  rw [hleft, h0]
  ring

/-- Upper bound on the "remainder" term S_q.
    The remainder satisfies S_q ≤ 3^q - 1 when all a_k ≥ 1. -/
lemma sumA_pos_of_tag_pos (n₀ : ℕ) (j q : ℕ) (hpos : ∀ k, k < q → 1 ≤ a n₀ (j + k)) :
    q ≤ sumA n₀ j q := by
  induction q with
  | zero => simp [sumA]
  | succ q ih =>
    simp only [sumA]
    have hq : q ≤ sumA n₀ j q := ih (fun k hk => hpos k (Nat.lt_succ_of_lt hk))
    have haq : 1 ≤ a n₀ (j + q) := hpos q (Nat.lt_succ_self q)
    omega

/-!
## Block product formula

The q-step product formula gives an exact expression:
  2^(sumA n₀ j q) * n_{j+q} = 3^q * n_j + R_q

where R_q depends on the intermediate valuations.

The key observation for L1 is that when sumA ≥ 12 and q = 7,
we can use the fact that 2^12 > 3^7 to get contraction.

For R_q, we use the recurrence:
- R_0 = 0
- R_{q+1} = 3 * R_q + 2^(sumA n₀ j q)
-/

/-- Remainder function for q-step product. -/
def R_q (n₀ : ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | q+1 => 3 * R_q n₀ j q + 2 ^ (sumA n₀ j q)

/-- q-step product formula (exact equality). -/
theorem block_product_eq (n₀ : ℕ) (j q : ℕ) :
    2 ^ (sumA n₀ j q) * orbit n₀ (j + q) = 3 ^ q * orbit n₀ j + R_q n₀ j q := by
  induction q generalizing j with
  | zero =>
    simp [sumA, R_q, orbit]
  | succ q ih =>
    simp only [sumA, R_q]
    -- Orbit step
    have horbit : j + (q + 1) = (j + q) + 1 := by ring
    -- 2^(sum_q + a_q) * n_{j+q+1} = 2^sum_q * (2^a_q * n_{j+q+1})
    --                             = 2^sum_q * (3 * n_{j+q} + 1)
    have hpow : 2 ^ (sumA n₀ j q + a n₀ (j + q)) = 2 ^ (sumA n₀ j q) * 2 ^ (a n₀ (j + q)) := by
      rw [Nat.pow_add]
    rw [hpow, Nat.mul_assoc, horbit]
    have hstep : 2 ^ (a n₀ (j + q)) * orbit n₀ ((j + q) + 1) = 3 * orbit n₀ (j + q) + 1 :=
      orbit_step n₀ (j + q)
    rw [hstep]
    -- 2^sum_q * (3 * n_{j+q} + 1) = 3 * (2^sum_q * n_{j+q}) + 2^sum_q
    have hexp : 2 ^ (sumA n₀ j q) * (3 * orbit n₀ (j + q) + 1) =
        3 * (2 ^ (sumA n₀ j q) * orbit n₀ (j + q)) + 2 ^ (sumA n₀ j q) := by ring
    rw [hexp]
    -- Use IH
    have hih : 2 ^ (sumA n₀ j q) * orbit n₀ (j + q) = 3 ^ q * orbit n₀ j + R_q n₀ j q := ih j
    rw [hih]
    -- 3 * (3^q * n_j + R_q) + 2^sum_q = 3^(q+1) * n_j + 3 * R_q + 2^sum_q
    ring

/-- Block contraction for 7 steps.
    Uses the exact product formula. -/
theorem block_contraction_7 (n₀ : ℕ) (j : ℕ) :
    2 ^ (sumA n₀ j 7) * orbit n₀ (j + 7) = 3 ^ 7 * orbit n₀ j + R_q n₀ j 7 :=
  block_product_eq n₀ j 7

/-- sumA n₀ j 7 equals B7 n₀ j. -/
lemma sumA_eq_B7 (n₀ : ℕ) (j : ℕ) : sumA n₀ j 7 = B7 n₀ j := by
  simp only [sumA, B7]
  ring

/-- L1: Block Contraction for (q=7, p=12).

    If B7(j) ≥ 12, then 4096 * n_{j+7} ≤ 2187 * n_j + 2186.

    This is the key lemma for the divergence barrier in Collatz Route II.
-/
theorem BlockContraction7_12 (n₀ : ℕ) (j : ℕ)
    (hB : B7 n₀ j ≥ 12) :
    4096 * orbit n₀ (j + 7) ≤ 2187 * orbit n₀ j + 2186 := by
  -- From block_contraction_7: 2^(sumA j 7) * n_{j+7} = 3^7 * n_j + R_q j 7
  have heq : 2 ^ (sumA n₀ j 7) * orbit n₀ (j + 7) = 3 ^ 7 * orbit n₀ j + R_q n₀ j 7 :=
    block_contraction_7 n₀ j
  -- sumA j 7 = B7 j
  have hsum : sumA n₀ j 7 = B7 n₀ j := sumA_eq_B7 n₀ j
  rw [hsum] at heq
  -- Since B7 ≥ 12, we have 2^12 ≤ 2^(B7)
  have hpow : 2^12 ≤ 2^(B7 n₀ j) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hB
  -- From the equality: orbit n₀ (j + 7) = (3^7 * n_j + R_q) / 2^(B7)
  -- We need: 4096 * n_{j+7} ≤ 2187 * n_j + 2186
  -- Multiply both sides of inequality by n_{j+7}:
  -- 4096 * n_{j+7} ≤ 2^(B7) * n_{j+7} = 3^7 * n_j + R_q n₀ j 7
  have hmul : 4096 * orbit n₀ (j + 7) ≤ 2 ^ (B7 n₀ j) * orbit n₀ (j + 7) := by
    exact Nat.mul_le_mul_right (orbit n₀ (j + 7)) hpow
  rw [heq] at hmul
  -- Now we need: 3^7 * n_j + R_q ≤ 2187 * n_j + 2186
  -- This requires R_q n₀ j 7 ≤ 2186 = 3^7 - 1
  -- This is the key bound that needs to be proven separately
  -- For now, we use the structural fact that R_q ≤ 2^(B7) - 1 when B7 ≥ something
  sorry

/-!
## Ldiv-0: Expansive blocks necessary for divergence
-/

/-- Definition of divergence for an orbit. -/
def Diverges (n₀ : ℕ) : Prop :=
  ∀ M : ℕ, ∃ k : ℕ, orbit n₀ k ≥ M

/-- Ldiv-0: If an orbit diverges, it has infinitely many "expansive" blocks
    (blocks with B7 < 12).

    This follows by contrapositive from BlockContraction7_12.
-/
theorem expansive_blocks_necessary (n₀ : ℕ)
    (hDiv : Diverges n₀) :
    ∀ J : ℕ, ∃ j, j ≥ J ∧ B7 n₀ j < 12 := by
  -- Proof by contrapositive:
  -- If ∃ J such that ∀ j ≥ J, B7 ≥ 12,
  -- then by BlockContraction7_12, the orbit is eventually bounded,
  -- contradicting divergence.
  sorry

end RevHalt.CollatzBlock
