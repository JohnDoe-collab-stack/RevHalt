/-
  RevHalt.Dynamics.Instances.OmegaKolmogorov

  EMERGENCE OF KOLMOGOROV COMPLEXITY FROM OMEGA DYNAMICS

  # Main Result

  K_gap(n) ≥ n : "To make the geometric residual gap(t)=1−OmegaApprox(t) fall below 2^{-n},
  one needs t ≥ n."

  # The Core Argument (Simple)

  1. OmegaApprox t ≤ 1 - 2^{-t}  (geometric series bound)
  2. Therefore: gap(t) = 1 - OmegaApprox(t) ≥ 2^{-t}
  3. To achieve precision 2^{-n} (gap ≤ 2^{-n}), we need 2^{-t} ≤ 2^{-n}, so t ≥ n
  4. The parameter t is the computational resource (time/fuel)
  5. Therefore: n bits of *dyadic precision toward 1* costs at least n

  This is the kinetic/arithmetic core: dyadic resolution 2^{-n} cannot be reached
  before time n (via the geometric tail).

  # Connection to omega_bit_cut_link

  The theorem omega_bit_cut_link shows:
    BitIs n a ↔ ∃ k, CutGe(k/2^n) ∧ ¬CutGe((k+1)/2^n) ∧ k%2=(a:ℕ)

  BitIs/WinDyad is equivalent to a dyadic window for OmegaApprox t (local semantics).
  The gap bound gives a lower bound on the time needed to reach cuts close to 1;
  it does not by itself certify stabilization of the limit-bit of Ω.
-/

import RevHalt.Dynamics.Instances.OmegaChaitin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity


namespace RevHalt.Dynamics.Instances.OmegaKolmogorov

open RevHalt.Dynamics.Instances.OmegaChaitin
open RevHalt
open Finset

/-!
## §1. The Gap Function

gap(t) = 1 - OmegaApprox t is the residual to the geometric upper bound 1
(tail of dyadic weights). It is NOT the error |Ω - OmegaApprox t|.
-/

/-- The gap (uncertainty) about Ω at time t. -/
def gap (t : ℕ) : ℚ := 1 - OmegaApprox t

/-- Gap is non-negative (OmegaApprox ≤ 1). -/
theorem gap_nonneg (t : ℕ) : 0 ≤ gap t := by
  simp only [gap]
  have h := OmegaApprox_le_one t
  linarith

/-- Gap decreases with time (OmegaApprox increases). -/
theorem gap_antimono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : gap t₂ ≤ gap t₁ := by
  simp only [gap]
  have := OmegaApprox_mono t₁ t₂ h
  linarith

/-!
## §2. The Fundamental Lower Bound

This is the KEY theorem: gap(t) ≥ 2^{-t}.

It follows from the geometric series:
  ∑_{p<t} 2^{-(p+1)} = 1 - 2^{-t}

Since OmegaApprox t ≤ this sum (not all programs halt),
we have gap(t) = 1 - OmegaApprox(t) ≥ 2^{-t}.
-/

/-- **KEY THEOREM**: The gap is bounded below by 2^{-t}.

This is the non-trivial arithmetic content from which the gap-based bound emerges.
-/
theorem gap_lower_bound (t : ℕ) : gap t ≥ (1 : ℚ) / 2^t := by
  simp only [gap]
  -- OmegaApprox t ≤ ∑_{p<t} omegaWeight p (each term is 0 if program doesn't halt)
  have h_bound : OmegaApprox t ≤ ∑ p ∈ range t, omegaWeight p := by
    unfold OmegaApprox
    apply sum_le_sum
    intro p _
    by_cases hH : haltsWithinDec t p 0 = true
    · simp [hH]
    · simp only [Bool.not_eq_true] at hH
      simp only [hH, omegaWeight]
      apply div_nonneg <;> positivity
  -- ∑_{p<t} omegaWeight p = 1 - 2^{-t}
  have h_sum : (∑ p ∈ range t, omegaWeight p) = 1 - (1 : ℚ) / 2^t := sum_weight_range_eq t
  -- Therefore: 1 - OmegaApprox t ≥ 1 - (1 - 2^{-t}) = 2^{-t}
  calc 1 - OmegaApprox t
      ≥ 1 - (∑ p ∈ range t, omegaWeight p) := by linarith
    _ = 1 - (1 - (1 : ℚ) / 2^t) := by rw [h_sum]
    _ = (1 : ℚ) / 2^t := by ring

/-!
## §3. Precision Requires Time

Corollary: To achieve n bits of precision, we need t ≥ n.
-/

/-- Resolution at level n is 2^{-n}. -/
def resolution (n : ℕ) : ℚ := (1 : ℚ) / 2^n

/-- **COROLLARY**: To achieve gap ≤ 2^{-n}, we need t ≥ n.

This is the formal statement of K_gap(n) ≥ n: dyadic resolution requires time.
-/
theorem precision_requires_time (t n : ℕ) (h_prec : gap t ≤ resolution n) : t ≥ n := by
  have h_gap := gap_lower_bound t
  have h_ineq : (1 : ℚ) / 2^t ≤ (1 : ℚ) / 2^n := by
    calc
      (1 : ℚ) / 2^t ≤ gap t := h_gap
      _ ≤ resolution n := h_prec
      _ = (1 : ℚ) / 2^n := rfl
  have h2t_pos : (0 : ℚ) < 2^t := by positivity
  have h2n_pos : (0 : ℚ) < 2^n := by positivity
  -- Clear denominators: (1/2^t ≤ 1/2^n) ↔ (2^n ≤ 2^t)
  have h_pow : (2 : ℚ)^n ≤ (2 : ℚ)^t := by
    have := (div_le_div_iff₀ h2t_pos h2n_pos).1 h_ineq
    simp [one_mul] at this
    exact this

  -- Since 1 < 2, exponent is monotone
  have h_one_lt_two : (1 : ℚ) < (2 : ℚ) := by norm_num
  exact (pow_le_pow_iff_right₀ h_one_lt_two).1 h_pow


/-- Equivalent form: if t < n then gap(t) > 2^{-n}. -/
theorem insufficient_time_means_insufficient_precision (t n : ℕ) (h : t < n) :
    gap t > resolution n := by
  by_contra h_neg
  push_neg at h_neg
  have := precision_requires_time t n h_neg
  omega

/-!
## §4. The Pure Kolmogorov Bound

The cleanest statement doesn't mention bits at all.

**IMPORTANT**: This theorem says:
  "To make OmegaApprox t ≥ 1 - 2^{-n}, time t ≥ n is required."

This is a Kolmogorov-style bound because:
- The exponent n measures "how close to 1" we want to get
- The time t measures computational resource
- The bound t ≥ n is tight (equality when all programs 0..t-1 halt)

This is NOT the classical Chaitin theorem K(Ω_n) ≥ n - c, which would require:
- Formalizing "program that computes the first n bits of Ω"
- Formalizing "program size" (Kolmogorov complexity)
- A self-referential compression argument

What we prove is a STRUCTURAL precursor: the arithmetic bound that makes
Chaitin's theorem possible.
-/

/--
**PURE GAP BOUND**:

To achieve precision 2^{-n} (i.e., gap ≤ 2^{-n}), computational time t ≥ n is required.

This is the kinetic/arithmetic core: dyadic resolution 2^{-n} cannot be reached
before time n (via the geometric tail).
-/
theorem kolmogorov_bound (n : ℕ) :
    ∀ t, gap t ≤ resolution n → t ≥ n :=
  fun t h => precision_requires_time t n h

/-!
## §5. Connection to Bits (Local Semantics)

The theorem `omega_bit_cut_link` (in OmegaChaitin.lean) shows:

```
OmegaSat t (BitIs n a) ↔
  ∃ k, OmegaSat t (CutGe(k/2^n)) ∧ ¬OmegaSat t (CutGe((k+1)/2^n)) ∧ k%2=(a:ℕ)
```

BitIs/WinDyad is equivalent to a dyadic window for OmegaApprox t (local semantics).
The gap bound gives a lower bound on the time needed to reach cuts close to 1;
it does NOT by itself certify stabilization of the limit-bit of Ω.

To satisfy `BitIs n a`, `OmegaApprox t` must be in the interval
`[k/2^n, (k+1)/2^n)` of width `2^{-n}`. The gap bound constrains how fast
we can approach 1, not how the bits of Ω stabilize.
-/

/-!
## Summary

The chain of reasoning:

```
sum_weight_range_eq          OmegaApprox t ≤ 1 - 2^{-t}
        ↓
gap_lower_bound              gap(t) ≥ 2^{-t}
        ↓
precision_requires_time      gap(t) ≤ 2^{-n} → t ≥ n
        ↓
kolmogorov_bound             K_gap(n) ≥ n (dyadic precision toward 1)
```

The key insight: the SAME parameter n appears as:
1. Exponent in the resolution 2^{-n}
2. Lower bound on computational time t

This is NOT circular because:
- sum_weight_range_eq is pure arithmetic (geometric series)
- gap_lower_bound uses the structure of omegaWeight = 2^{-(p+1)}
- precision_requires_time is arithmetic manipulation

Note: This is NOT the classical Chaitin theorem K(Ω_n) ≥ n - c about bits of Ω.
We prove a structural precursor about the gap to the geometric bound.
-/

end RevHalt.Dynamics.Instances.OmegaKolmogorov
