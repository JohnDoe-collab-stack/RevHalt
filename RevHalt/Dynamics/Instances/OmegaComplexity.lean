/-
  RevHalt.Dynamics.Instances.OmegaComplexity

  Bridge between Complexity (abstract) and OmegaChaitin (concrete).

  Key insight: measuring "precision" via BitIs is subtle because
  BitIs m 0 is trivially true at t=0 (floor of 0 is 0, 0 % 2 = 0).

  The meaningful measure is PrecisionCertificate: a STRICT window on Ω.
-/

import RevHalt.Dynamics.Core.Complexity
import RevHalt.Dynamics.Instances.OmegaChaitin

namespace RevHalt.Dynamics.Instances.OmegaComplexity

open RevHalt.Dynamics.Core
open RevHalt.Dynamics.Core.Complexity
open RevHalt.Dynamics.Instances.OmegaChaitin

/-!
  ## 1. Precision = Strict Windows

  A precision certificate witnesses that Ω lies in a STRICT dyadic interval.
  This is different from BitIs which can be trivially satisfied.
-/

/-- A precision certificate: proof that Ω is strictly localized.
    The window [k/2^n, (k+1)/2^n) has width 2^{-n}.
    Key requirement: the window is NON-TRIVIAL (k > 0 or strict bounds). -/
structure PrecisionCertificate where
  n : ℕ                    -- Precision (number of bits)
  t : ℕ                    -- Time step
  k : ℕ                    -- Window index (non-negative for meaningful info)
  lower_bound : OmegaApprox t ≥ (k : ℚ) / (2 ^ n)
  upper_bound : OmegaApprox t < ((k + 1) : ℚ) / (2 ^ n)

/-- Precision from a certificate. -/
def certificate_precision (c : PrecisionCertificate) : ℕ := c.n

/-!
  ## 2. The Key Lemma: Window Width Requires Steps

  For OmegaApprox t to lie in a window [k/2^n, (k+1)/2^n) with k > 0,
  we need OmegaApprox t ≥ k/2^n > 0.

  The maximum value of OmegaApprox t is bounded by sum of weights
  of halting programs up to t, which is at most 1 - 2^{-t}.

  For a non-trivial window at precision n, we need at least
  some program to have halted, which requires t ≥ 1.
-/

/-- Upper bound on OmegaApprox. -/
theorem omega_approx_upper_bound (t : ℕ) :
    OmegaApprox t ≤ 1 - (1 : ℚ) / (2 ^ t) := by
  have h := OmegaApprox_le_one t
  have hsum := sum_weight_range_eq t
  -- OmegaApprox t ≤ ∑ omegaWeight ≤ 1 - 2^{-t}
  classical
  calc OmegaApprox t
      ≤ ∑ p ∈ Finset.range t, omegaWeight p := by
        unfold OmegaApprox
        apply Finset.sum_le_sum
        intro p _
        by_cases hH : haltsWithin t p 0
        · simp only [if_pos hH, le_refl]
        · simp only [if_neg hH, omegaWeight]
          apply div_nonneg
          · norm_num
          · apply pow_nonneg; norm_num
    _ = 1 - (1 : ℚ) / (2 ^ t) := hsum

/-- A positive lower bound requires time steps.
    If OmegaApprox t ≥ q > 0, then t > 0. -/
theorem positive_requires_steps {t : ℕ} {q : ℚ} (hq : 0 < q)
    (h : OmegaApprox t ≥ q) : 0 < t := by
  by_contra hcontra
  push_neg at hcontra
  have ht0 : t = 0 := Nat.eq_zero_of_le_zero hcontra
  rw [ht0] at h
  simp only [OmegaApprox, Finset.range_zero, Finset.sum_empty] at h
  linarith

/-!
  ## 3. Main Theorem: Precision Requires Cost

  If we have a precision certificate with k > 0
  (meaning we've actually localized Ω above 0),
  then the time t must be positive.

  More precisely: for precision n with k ≥ 1, we need t ≥ 1.

  The deeper theorem (t ≥ n) would require showing that
  each unit of time gives at most one bit of precision.
-/

/-- Non-trivial precision requires steps. -/
theorem nontrivial_precision_requires_steps (cert : PrecisionCertificate)
    (h_nontrivial : cert.k ≥ 1) : cert.t > 0 := by
  have hpos : (0 : ℚ) < (cert.k : ℚ) / (2 ^ cert.n) := by
    apply div_pos
    · exact Nat.cast_pos.mpr h_nontrivial
    · exact pow_pos (by norm_num : (0 : ℚ) < 2) cert.n
  exact positive_requires_steps hpos cert.lower_bound

/-!
  ## 4. The Structural Bound: t ≥ n

  Key insight: OmegaApprox t is a sum of terms 2^{-(p+1)} for p < t.
  The smallest such term is 2^{-t} (for p = t-1).

  Therefore, OmegaApprox t can only take values that are multiples of 2^{-t}.
  To distinguish windows of width 2^{-n}, we need 2^{-t} ≤ 2^{-n}, i.e., t ≥ n.

  More precisely: the DIFFERENCE between any two distinct values of OmegaApprox
  at the same time step t is at least 2^{-t} (the smallest weight).
-/

/-- The minimum non-zero weight at time t is omegaWeight (t-1) = 2^{-t}. -/
theorem min_weight_at_time (t : ℕ) (ht : t > 0) :
    ∃ p < t, omegaWeight p = (1 : ℚ) / (2 ^ (p + 1)) ∧
             ∀ q < t, omegaWeight q ≥ omegaWeight (t - 1) := by
  use t - 1
  constructor
  · exact Nat.sub_one_lt_of_le ht (le_refl t)
  constructor
  · rfl
  · intro q hq
    simp only [omegaWeight]
    -- Need: 1 / 2^(q+1) ≥ 1 / 2^t
    -- Since q < t, we have q + 1 ≤ t, so 2^(q+1) ≤ 2^t, so 1/2^(q+1) ≥ 1/2^t
    apply one_div_le_one_div_of_le
    · apply pow_pos; norm_num
    · have hle : q + 1 ≤ t := hq
      have hpow : (2 : ℕ) ^ (q + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle
      have ht_eq : t - 1 + 1 = t := Nat.sub_add_cancel ht
      rw [ht_eq]
      exact mod_cast hpow

/-- Resolution bound: for NON-TRIVIAL precision (k ≥ 1), we need t ≥ n.

    Proof:
    - cert.lower_bound says: Ω_t ≥ k/2^n
    - If k ≥ 1, then Ω_t ≥ 1/2^n > 0
    - But Ω_t ≤ 1 - 1/2^t (by omega_approx_upper_bound)
    - And all terms in Ω_t are of form 2^{-(p+1)} for p < t
    - The smallest positive value of Ω_t is 2^{-t} (when only program t-1 halts)
    - If Ω_t ≥ 1/2^n and the smallest step is 2^{-t}, we need 2^{-t} ≤ 1/2^n
    - This gives t ≥ n
-/
theorem precision_requires_cost_nontrivial (cert : PrecisionCertificate)
    (h_nontrivial : cert.k ≥ 1) : cert.t ≥ cert.n := by
  -- From h_nontrivial and cert.lower_bound: Ω_t ≥ k/2^n ≥ 1/2^n
  have hpos : OmegaApprox cert.t ≥ (1 : ℚ) / (2 ^ cert.n) := by
    calc OmegaApprox cert.t
        ≥ (cert.k : ℚ) / (2 ^ cert.n) := cert.lower_bound
      _ ≥ (1 : ℚ) / (2 ^ cert.n) := by
        apply div_le_div_of_nonneg_right
        · exact Nat.one_le_cast.mpr h_nontrivial
        · apply pow_nonneg; norm_num

  -- And Ω_t ≤ 1 - 1/2^t
  have hbound := omega_approx_upper_bound cert.t

  -- So 1/2^n ≤ Ω_t ≤ 1 - 1/2^t < 1
  -- For t = 0: Ω_0 = 0, but we have Ω_t > 0, so t > 0 (already proven)
  have ht_pos := nontrivial_precision_requires_steps cert h_nontrivial

  -- Now we need: 1/2^n ≤ 1 - 1/2^t
  -- Rearranging: 1/2^t ≤ 1 - 1/2^n < 1
  -- So: 1/2^t + 1/2^n ≤ 1

  -- The key insight: if Ω_t ≥ 1/2^n and Ω_t ≤ 1 - 1/2^t,
  -- then 1/2^n ≤ 1 - 1/2^t, i.e., 1/2^t + 1/2^n ≤ 1.

  -- From this we can derive n ≤ t? Not directly...
  -- Actually, for n > t: 1/2^n < 1/2^t, so 1/2^n + 1/2^t < 2/2^t ≤ 1 when t ≥ 1.
  -- So the constraint 1/2^n ≤ 1 - 1/2^t is not enough.

  -- The real proof needs the discretization structure.
  -- For now, we use sorry with a clear note about what's needed.
  sorry

/-!
  ## 5. Summary

  We have established:
  1. `PrecisionCertificate`: meaningful localization of Ω
  2. `positive_requires_steps`: any progress requires t > 0
  3. `nontrivial_precision_requires_steps`: k ≥ 1 → t > 0
  4. `precision_requires_cost_nontrivial`: n bits → n steps (with sorry)

  This captures the intuition that Omega's bits are revealed
  progressively, at most one per time step.
-/

#check precision_requires_cost_nontrivial
#check nontrivial_precision_requires_steps

end RevHalt.Dynamics.Instances.OmegaComplexity
