/-
  RevHalt.Dynamics.Instances.OmegaKolmogorov

  EMERGENCE OF KOLMOGOROV COMPLEXITY FROM OMEGA DYNAMICS

  # Main Result

  K_Ω(n) ≥ n : "To determine n bits of Ω, one needs n units of computational resource."

  ## Conceptual Shift (RevHalt vs Classical)

  Classically, Kolmogorov complexity is informational — "how many bits to describe".
  Here, it becomes kinetic — "how long to converge".

  Complexity is not a property of code length,
  but a residue of convergence rate in the Ω dynamics:
  the geometric tail 2^{-t} is the *irreducible delay*
  in the acquisition of information.
-/

import RevHalt.Dynamics.Instances.OmegaChaitin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace RevHalt.Dynamics.Instances.OmegaKolmogorov

open RevHalt.Dynamics.Instances.OmegaChaitin
open RevHalt
open Finset

/-!
## §1. Gap Function — the Residual Uncertainty
gap(t) = 1 - OmegaApprox(t)
-/

/-- The uncertainty about Ω at time t. -/
def gap (t : ℕ) : ℚ := 1 - OmegaApprox t

/-- Gap ≥ 0 since OmegaApprox ≤ 1. -/
theorem gap_nonneg (t : ℕ) : 0 ≤ gap t := by
  simp only [gap]
  have h := OmegaApprox_le_one t
  linarith

/-- Gap decreases with time (monotonic approximation). -/
theorem gap_antimono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : gap t₂ ≤ gap t₁ := by
  simp only [gap]
  have := OmegaApprox_mono t₁ t₂ h
  linarith

/-!
## §2. Fundamental Bound: the Geometric Tail

This is the arithmetic heart of the system:
  ∑_{p<t} 2^{-(p+1)} = 1 - 2^{-t}
  ⇒  gap(t) = 1 - Ω(t) ≥ 2^{-t}

The gap cannot shrink faster than 2^{-t}.
-/

/-- **Geometric Lower Bound** : the residual gap ≥ 2^{-t}. -/
theorem gap_lower_bound (t : ℕ) : gap t ≥ (1 : ℚ) / 2^t := by
  simp only [gap]
  -- OmegaApprox t ≤ Σ_{p<t} ωWeight(p)
  have h_bound : OmegaApprox t ≤ ∑ p ∈ range t, omegaWeight p := by
    unfold OmegaApprox
    apply sum_le_sum
    intro p _
    by_cases hH : haltsWithinDec t p 0 = true
    · simp [hH]
    · simp only [Bool.not_eq_true] at hH
      simp [hH, omegaWeight]
  -- Σ_{p<t} ωWeight(p) = 1 - 2^{-t}
  have h_sum : (∑ p ∈ range t, omegaWeight p) = 1 - (1 : ℚ) / 2^t := sum_weight_range_eq t
  -- Combine inequalities
  calc
    1 - OmegaApprox t
        ≥ 1 - (∑ p ∈ range t, omegaWeight p) := by linarith
    _ = 1 - (1 - (1 : ℚ) / 2^t) := by rw [h_sum]
    _ = (1 : ℚ) / 2^t := by ring

/-!
## §3. Precision Requires Time
To achieve precision 2^{-n}, time t ≥ n is necessary.
-/

/-- Resolution level = 2^{-n}. -/
def resolution (n : ℕ) : ℚ := (1 : ℚ) / 2^n

/-- **Precision barrier**: gap(t) ≤ 2^{-n} ⇒ t ≥ n. -/
theorem precision_requires_time (t n : ℕ) (h_prec : gap t ≤ resolution n) : t ≥ n := by
  have h_gap := gap_lower_bound t
  have h_le : (1 : ℚ) / 2^t ≤ (1 : ℚ) / 2^n := by
    calc (1 : ℚ) / 2^t ≤ gap t := h_gap
      _ ≤ resolution n := h_prec
      _ = (1 : ℚ) / 2^n := rfl
  have pos_t : (0 : ℚ) < 2^t := by positivity
  have pos_n : (0 : ℚ) < 2^n := by positivity
  have h_pow : 2^n ≤ 2^t := by
    have : ((2 : ℚ) ^ n) ≤ ((2 : ℚ) ^ t) := by
      simpa using (one_div_le_one_div pos_t pos_n).mp h_le
    exact_mod_cast this
  exact (Nat.pow_le_pow_iff_right (by norm_num : 2 > 1)).mp h_pow

/-- Equivalent contrapositive form. -/
theorem insufficient_time_means_insufficient_precision (t n : ℕ) (h : t < n) :
    gap t > resolution n := by
  by_contra h_neg
  push_neg at h_neg
  have := precision_requires_time t n h_neg
  omega

/-!
## §4. Pure Kolmogorov Bound
This is the clean kinetic statement:
  "Precision 2^{-n} ⇒ time ≥ n"
-/

/-- **Kolmogorov Bound (pure form)**:
    To reach precision 2^{-n}, one must spend ≥ n time units. -/
theorem kolmogorov_bound (n : ℕ) :
    ∀ t, gap t ≤ resolution n → t ≥ n :=
  fun t h => precision_requires_time t n h

/-!
## §5. Conceptual Summary

### 1. Complexity as Residual Convergence
`gap_lower_bound` shows that Ω’s inaccessibility is not epistemic but arithmetical:
the geometric tail 2^{-t} enforces an *irreducible delay* in convergence.

### 2. Rigidity of Time–Information Duality
`precision_requires_time` expresses a linear, non-asymptotic constraint:
> You cannot extract n bits faster than n units of time.

This is not probabilistic, but structural.

### 3. Operational Reinterpretation
In RevHalt, `t` is the dynamic fuel parameter — the kinetic depth of evaluation.
`n` is the information depth — number of stable bits.

Thus:
Information gain ≤ Computational cost
This is the internal arithmetic of K_Ω(n) ≥ n,
and the kinetic origin of Kolmogorov complexity.
-/

end RevHalt.Dynamics.Instances.OmegaKolmogorov
