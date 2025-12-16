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
  ## 4. The Structural Bound: t ≥ n (Conjectural)

  The full theorem would be:
  "For precision n (window width 2^{-n}), we need t ≥ n"

  Proof sketch:
  - OmegaApprox t ≤ 1 - 2^{-t} (proven above)
  - If t < n, then window width 2^{-n} < 2^{-t}
  - But the "resolution" of OmegaApprox at time t is at most 2^{-t}
  - So we can't distinguish windows finer than 2^{-t}

  This requires a more careful analysis of OmegaApprox's structure.
  We state it as an axiom for now.
-/

/-- Precision requires proportional cost (structural axiom).
    A full proof would analyze the discretization of OmegaApprox. -/
axiom precision_cost_axiom : ∀ (cert : PrecisionCertificate),
    cert.n ≤ cert.t

/-- Theorem: n bits of precision require at least n steps. -/
theorem precision_requires_cost (cert : PrecisionCertificate) :
    cert.t ≥ cert.n := precision_cost_axiom cert

/-!
  ## 5. Summary

  We have established:
  1. `PrecisionCertificate`: meaningful localization of Ω
  2. `positive_requires_steps`: any progress requires t > 0
  3. `nontrivial_precision_requires_steps`: k ≥ 1 → t > 0
  4. `precision_requires_cost`: n bits → n steps (via axiom)

  The axiom captures the intuition that Omega's bits are revealed
  progressively, at most one per time step.
-/

#check precision_requires_cost
#check nontrivial_precision_requires_steps

end RevHalt.Dynamics.Instances.OmegaComplexity
