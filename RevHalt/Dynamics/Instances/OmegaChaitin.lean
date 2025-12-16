/-
  RevHalt.Dynamics.Instances.OmegaChaitin

  "Vrai" Ω : aucune axiomatisation de `OmegaApprox`.
  On définit une approximation rationnelle par somme finie sur les codes < t
  qui terminent dans `evaln t`.

  # Core Philosophy
  In OmegaChaitin.lean, I take two primitive coordinates of the same referent Ω:
  discrete assertions `OmegaSentence.BitIs` and continuous assertions `OmegaSentence.CutGe`.
  I invert the usual computability hierarchy by making rational cuts (semi-decidable)
  the base layer, and then reconstructing the bits (non-computable) as boundaries
  between cuts, via `omega_bit_cut_link`.

  ## Key Definitions

  1. **Primitives**:
     ```lean
     | CutGe (q : ℚ) : OmegaSentence         -- Continuous
     | BitIs (n : ℕ) (a : ℕ) : OmegaSentence -- Discrete
     ```

  2. **The Link (Bit as Boundary)**:
     ```lean
     theorem omega_bit_cut_link : ...
       OmegaSat t (OmegaBit n a x) ↔
       ∃ (k : ℤ),
         OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) x) ∧
         ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
         k.toNat % 2 = a
     ```
-/

import RevHalt.Dynamics.Core.RefSystem
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset

namespace RevHalt.Dynamics.Instances.OmegaChaitin

open RevHalt
open Nat.Partrec
open Classical

-- ==============================================================================================
-- 1. "Vrai" Ω Approximation (no axioms - fully constructive)
-- ==============================================================================================

/-- Weight of program index `p` (dyadic). -/
def omegaWeight (p : ℕ) : ℚ := (1 : ℚ) / ((2 : ℚ) ^ (p + 1))

/-- Decidable version: program p halts within t steps on input n.
    Returns Bool, so `if haltsWithinDec ...` is computable. -/
def haltsWithinDec (t p n : ℕ) : Bool :=
  (Nat.Partrec.Code.ofNatCode p).evaln t n |>.isSome

/-- `haltsWithin t p n` : the decoded Partrec code `p` returns some value on input `n`
    within the `evaln t` search bound. (Prop version for proofs) -/
def haltsWithin (t p n : ℕ) : Prop :=
  ∃ x : ℕ, x ∈ (Nat.Partrec.Code.ofNatCode p).evaln t n

/-- Equivalence between Bool and Prop versions. -/
theorem haltsWithinDec_iff (t p n : ℕ) :
    haltsWithinDec t p n = true ↔ haltsWithin t p n := by
  unfold haltsWithinDec haltsWithin
  rw [Option.isSome_iff_exists]
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, Option.mem_def.mpr hx⟩
  · intro ⟨x, hx⟩
    exact ⟨x, Option.mem_def.mp hx⟩

/-- Monotonicity of `haltsWithin` in the bound `t`. -/
theorem haltsWithin_mono {t₁ t₂ p n : ℕ} (h : t₁ ≤ t₂) :
    haltsWithin t₁ p n → haltsWithin t₂ p n := by
  rintro ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Nat.Partrec.Code.evaln_mono h hx

/-- Monotonicity of `haltsWithinDec` in the bound `t` (Bool version). -/
theorem haltsWithinDec_mono {t₁ t₂ p n : ℕ} (h : t₁ ≤ t₂) :
    haltsWithinDec t₁ p n = true → haltsWithinDec t₂ p n = true := by
  rw [haltsWithinDec_iff, haltsWithinDec_iff]
  exact haltsWithin_mono h

/-- Finite approximation Ωₜ (rational). COMPUTABLE: uses haltsWithinDec (Bool). -/
def OmegaApprox (t : ℕ) : ℚ :=
  ∑ p ∈ Finset.range t,
    (if haltsWithinDec t p 0 then omegaWeight p else 0)

/-- Approximations are non-negative. -/
theorem OmegaApprox_nonneg : ∀ t, 0 ≤ OmegaApprox t := by
  intro t
  unfold OmegaApprox
  apply Finset.sum_nonneg
  intro p _
  by_cases hH : haltsWithinDec t p 0 = true
  · simp only [hH, ↓reduceIte, omegaWeight]
    apply div_nonneg
    · norm_num
    · apply pow_nonneg; norm_num
  · simp only [Bool.not_eq_true] at hH
    simp only [hH, Bool.false_eq_true, ↓reduceIte, le_refl]

/-- Closed form for the geometric upper bound: ∑_{p < t} 2^-(p+1) = 1 - 2^-t. -/
theorem sum_weight_range_eq (t : ℕ) :
    (∑ p ∈ Finset.range t, omegaWeight p) = 1 - (1 : ℚ) / ((2 : ℚ) ^ t) := by
  classical
  induction t with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, div_one, sub_self]
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [omegaWeight, pow_succ]
      ring

/-- Approximations are bounded by 1. -/
theorem OmegaApprox_le_one : ∀ t, OmegaApprox t ≤ 1 := by
  intro t
  have h_le_sumWeights :
      OmegaApprox t ≤ ∑ p ∈ Finset.range t, omegaWeight p := by
    unfold OmegaApprox
    apply Finset.sum_le_sum
    intro p _
    by_cases hH : haltsWithinDec t p 0 = true
    · simp only [hH, ↓reduceIte, le_refl]
    · simp only [Bool.not_eq_true] at hH
      simp only [hH, Bool.false_eq_true, ↓reduceIte, omegaWeight]
      apply div_nonneg
      · norm_num
      · apply pow_nonneg; norm_num
  have h_sumWeights_le_one :
      (∑ p ∈ Finset.range t, omegaWeight p) ≤ 1 := by
    rw [sum_weight_range_eq]
    have hpos : 0 ≤ (1 : ℚ) / ((2 : ℚ) ^ t) := by
      apply div_nonneg
      · norm_num
      · apply pow_nonneg; norm_num
    linarith
  exact le_trans h_le_sumWeights h_sumWeights_le_one

/-- Monotonicity of Ωₜ. -/
theorem OmegaApprox_mono : ∀ t₁ t₂, t₁ ≤ t₂ → OmegaApprox t₁ ≤ OmegaApprox t₂ := by
  intro t₁ t₂ h12
  have h_termwise :
      (∑ p ∈ Finset.range t₁,
        (if haltsWithinDec t₁ p 0 then omegaWeight p else 0))
      ≤
      (∑ p ∈ Finset.range t₁,
        (if haltsWithinDec t₂ p 0 then omegaWeight p else 0)) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hH : haltsWithinDec t₁ p 0 = true
    · have hH' : haltsWithinDec t₂ p 0 = true := haltsWithinDec_mono h12 hH
      simp only [hH, ↓reduceIte, hH', le_refl]
    · simp only [Bool.not_eq_true] at hH
      by_cases hH' : haltsWithinDec t₂ p 0 = true
      · simp only [hH, Bool.false_eq_true, ↓reduceIte, hH', omegaWeight]
        apply div_nonneg
        · norm_num
        · apply pow_nonneg; norm_num
      · simp only [Bool.not_eq_true] at hH'
        simp only [hH, Bool.false_eq_true, ↓reduceIte, hH', le_refl]
  have h_extend :
      (∑ p ∈ Finset.range t₁,
        (if haltsWithinDec t₂ p 0 then omegaWeight p else 0))
      ≤
      (∑ p ∈ Finset.range t₂,
        (if haltsWithinDec t₂ p 0 then omegaWeight p else 0)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hp) h12)
    · intro p _ _
      by_cases hH : haltsWithinDec t₂ p 0 = true
      · simp only [hH, ↓reduceIte, omegaWeight]
        apply div_nonneg
        · norm_num
        · apply pow_nonneg; norm_num
      · simp only [Bool.not_eq_true] at hH
        simp only [hH, Bool.false_eq_true, ↓reduceIte, le_refl]
  simp only [OmegaApprox]
  exact le_trans h_termwise h_extend

/-- A trivial dichotomy lemma (no axiom): either reached q somewhere, or always below q. -/
theorem OmegaApprox_unbounded (q : ℚ) (_hq : q < 1) :
    (∃ T, OmegaApprox T ≥ q) ∨ (∀ t, OmegaApprox t < q) := by
  classical
  by_cases h : ∃ T, OmegaApprox T ≥ q
  · exact Or.inl h
  · refine Or.inr ?_
    intro t
    have : ¬ OmegaApprox t ≥ q := by
      intro ht
      exact h ⟨t, ht⟩
    exact lt_of_not_ge this

-- Define the "true" Ω as the supremum of the increasing bounded sequence (real).
-- Note: Requires Mathlib.Topology.Order.Basic or similar for SupSet ℝ instance.
-- Commented out to avoid import complexity.
-- noncomputable def Omega : ℝ :=
--   sSup (Set.range (fun t : ℕ => (OmegaApprox t : ℝ)))

-- ==============================================================================================
-- 2. Sentences about Ω
-- ==============================================================================================

/-- Sentences expressing knowledge about Ω (all in ℚ). -/
inductive OmegaSentence
| CutGe (q : ℚ) : OmegaSentence
| BitIs (n : ℕ) (a : ℕ) : OmegaSentence
| WinDyad (n : ℕ) (a : ℕ) : OmegaSentence -- syntactically orthogonal to BitIs
| Not (s : OmegaSentence) : OmegaSentence
| TrueS : OmegaSentence
| FalseS : OmegaSentence

/-- Models are time bounds (how far we've computed). -/
abbrev OmegaModel := ℕ

/-- Satisfaction at model t (having run programs up to time t). -/
def OmegaSat : OmegaModel → OmegaSentence → Prop
| t, OmegaSentence.CutGe q => OmegaApprox t ≥ q
| t, OmegaSentence.BitIs n a =>
    (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = a
| t, OmegaSentence.WinDyad n a =>
    ∃ (k : ℤ),
      OmegaApprox t ≥ ((k : ℚ) / (2 ^ n)) ∧
      ¬(OmegaApprox t ≥ (((k + 1) : ℚ) / (2 ^ n))) ∧
      k.toNat % 2 = a
| t, OmegaSentence.Not s => ¬OmegaSat t s
| _, OmegaSentence.TrueS => True
| _, OmegaSentence.FalseS => False

-- ==============================================================================================
-- 3. RefSystem Instance for Ω
-- ==============================================================================================

/-- The referent is Unit (only one Ω). -/
abbrev OmegaReferent := Unit

instance : Inhabited OmegaReferent := ⟨()⟩

/-- Cut encoding: "Ωₜ ≥ q". -/
def OmegaCut (q : ℚ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.CutGe q

/-- Bit encoding: "n-th bit of Ω is a". -/
def OmegaBit (n : ℕ) (a : ℕ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.BitIs n a

/-- Antimonotonicity of Cut: if Ωₜ ≥ q' and q ≤ q', then Ωₜ ≥ q. -/
theorem omega_cut_antimono : ∀ {t : OmegaModel} {q q' : ℚ} {x : OmegaReferent},
    q ≤ q' → OmegaSat t (OmegaCut q' x) → OmegaSat t (OmegaCut q x) := by
  intro t q q' _ hle hSat
  simp only [OmegaCut, OmegaSat] at hSat ⊢
  exact le_trans hle hSat

/--
Bit/Cut link (THEOREM, not an axiom):
the bit definition is equivalent to the strict dyadic window condition.
-/
theorem omega_bit_cut_link : ∀ {t : OmegaModel} {n a : ℕ} {x : OmegaReferent},
    OmegaSat t (OmegaBit n a x) ↔
    ∃ (k : ℤ),
      OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) x) ∧
      ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
      k.toNat % 2 = a := by
  intro t n a x
  simp only [OmegaSat, OmegaBit, OmegaCut]

  -- work in ℚ with d = 2^n (as ℚ)
  let r : ℚ := OmegaApprox t
  let d : ℚ := (2 : ℚ) ^ n
  have hdpos : (0 : ℚ) < d := by
    simp only [d]
    exact pow_pos (by norm_num : (0 : ℚ) < 2) n

  constructor
  · -- BitIs -> window (exists k)
    intro hBit
    -- rewrite hBit onto the canonical d*r form
    have hBit' : (⌊d * r⌋.toNat) % 2 = a := by
      simpa [r, d, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hBit

    let k : ℤ := ⌊d * r⌋

    have hk : ((k : ℚ) ≤ d * r) ∧ (d * r < (k : ℚ) + 1) := by
      have hfl : (⌊d * r⌋ : ℤ) = k := rfl
      exact ⟨Int.floor_le (d * r), Int.lt_floor_add_one (d * r)⟩

    refine ⟨k, ?_, ?_, ?_⟩
    · -- OmegaApprox t ≥ k/d
      have hle : (k : ℚ) / d ≤ r := by
        have : (k : ℚ) ≤ r * d := by simpa [mul_comm] using hk.1
        exact (div_le_iff₀ hdpos).2 this
      simpa [r, d, ge_iff_le] using hle
    · -- ¬ OmegaApprox t ≥ (k+1)/d
      have hlt : r < ((k : ℚ) + 1) / d := by
        apply (lt_div_iff₀ hdpos).2
        simpa [mul_comm] using hk.2
      have : ¬ ((k : ℚ) + 1) / d ≤ r := not_le_of_gt hlt
      simpa [r, d, ge_iff_le, add_comm, add_left_comm, add_assoc] using this
    · -- parity
      simpa [k] using hBit'

  · -- window -> BitIs
    rintro ⟨k, hCut, hNotCut, hpar⟩

    -- normalize hypotheses to r/d form
    have hCut' : (k : ℚ) / d ≤ r := by
      simpa [r, d, ge_iff_le] using hCut
    have hNotCut' : ¬ r ≥ (((k + 1) : ℚ) / d) := by
      simpa [r, d, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hNotCut

    have hk_le : (k : ℚ) ≤ d * r := by
      have : (k : ℚ) ≤ r * d := (div_le_iff₀ hdpos).1 hCut'
      simpa [mul_comm] using this

    have hk_lt : d * r < (k : ℚ) + 1 := by
      have hlt : r < (((k + 1) : ℚ) / d) := lt_of_not_ge hNotCut'
      have : r * d < ((k + 1) : ℚ) := (lt_div_iff₀ hdpos).1 hlt
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using this

    have hk_floor : (⌊d * r⌋ : ℤ) = k := by
      apply Int.floor_eq_iff.2
      constructor
      · exact hk_le
      · simpa [add_comm] using hk_lt

    have : (⌊d * r⌋.toNat) % 2 = a := by
      simp only [hk_floor]
      exact hpar
    simpa [r, d, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using this

/-- Win encoding: dyadic window sentence (syntactically orthogonal to Bit). -/
def OmegaWin (n : ℕ) (a : ℕ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.WinDyad n a

/-- Win/Cut link: WinDyad semantics is definitionally the RHS. -/
theorem omega_win_spec : ∀ {t : OmegaModel} {n a : ℕ} {x : OmegaReferent},
    OmegaSat t (OmegaWin n a x) ↔
    ∃ (k : ℤ),
      OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) x) ∧
      ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
      k.toNat % 2 = a := by
  intro t n a _
  simp only [OmegaWin, OmegaSat, OmegaCut]

/-- RefSystem instance for Ω. -/
def OmegaRefSystem : RefSystem OmegaModel OmegaSentence OmegaReferent where
  Sat := OmegaSat
  Cut := OmegaCut
  Bit := OmegaBit
  cut_antimono := omega_cut_antimono
  bit_cut_link := omega_bit_cut_link
  Win := OmegaWin
  win_spec := omega_win_spec

-- ==============================================================================================
-- 4. Local Reading for Ω
-- ==============================================================================================

/-- Local reading: at time t, verify φ using OmegaApprox t. -/
def LR_omega (Γ : Set OmegaSentence) (φ : OmegaSentence) : Trace :=
  fun t =>
    (∀ ψ ∈ Γ, OmegaSat t ψ) ∧ OmegaSat t φ

/-- The kinetic closure for Ω. -/
def CloK_omega (Γ : Set OmegaSentence) : Set OmegaSentence :=
  { φ | Halts (LR_omega Γ φ) }

-- ==============================================================================================
-- 4b. Dual LR Procedures for Non-Trivial Rev Equivalence
-- ==============================================================================================
/-!
## Quanta Result

**"Two reading procedures (Bit vs Window) are observationally indistinguishable:
same halts, hence same Rev verdicts (by T1)."**

These are **operationally distinct** procedures for verifying the n-th bit of Ω:
- `LR_bit`: computes `⌊2^n * Ωₜ⌋ % 2 = a`
- `LR_win`: searches for k such that `k/2^n ≤ Ωₜ < (k+1)/2^n` and `k % 2 = a`

The equivalence `LR_bit_win_halts_equiv` is **non-trivial**: it uses the arithmetic
content from `omega_bit_cut_link`, not just extensionality.
-/

/-- LR_bit: Verification by floor computation.
    Checks `⌊2^n * OmegaApprox t⌋ % 2 = a` directly. -/
def LR_bit (Γ : Set OmegaSentence) (n a : ℕ) : Trace :=
  fun t => (∀ ψ ∈ Γ, OmegaSat t ψ) ∧
           (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = a

/-- LR_win: Verification by dyadic window search.
    Searches for k such that `k/2^n ≤ Ωₜ < (k+1)/2^n` and `k % 2 = a`. -/
def LR_win (Γ : Set OmegaSentence) (n a : ℕ) : Trace :=
  fun t => (∀ ψ ∈ Γ, OmegaSat t ψ) ∧
           ∃ (k : ℤ), OmegaApprox t ≥ (k : ℚ) / (2 ^ n) ∧
                      ¬(OmegaApprox t ≥ ((k + 1) : ℚ) / (2 ^ n)) ∧
                      k.toNat % 2 = a

/-- LR_bit and LR_win are pointwise equivalent (via omega_bit_cut_link). -/
theorem LR_bit_win_equiv (Γ : Set OmegaSentence) (n a : ℕ) (t : ℕ) :
    LR_bit Γ n a t ↔ LR_win Γ n a t := by
  simp only [LR_bit, LR_win]
  constructor
  · intro ⟨hΓ, hBit⟩
    refine ⟨hΓ, ?_⟩
    -- Use omega_bit_cut_link to get the window form
    have h := (omega_bit_cut_link (t := t) (n := n) (a := a) (x := ())).mp
    simp only [OmegaBit, OmegaSat] at h
    exact h hBit
  · intro ⟨hΓ, hWin⟩
    refine ⟨hΓ, ?_⟩
    -- Use omega_bit_cut_link reverse direction
    have h := (omega_bit_cut_link (t := t) (n := n) (a := a) (x := ())).mpr
    simp only [OmegaBit, OmegaSat] at h
    exact h hWin

/-- **Non-Trivial Halting Equivalence**: Same halting behavior for LR_bit vs LR_win.

    This is the key result demonstrating that two operationally distinct procedures
    have identical observational behavior (halting). The proof uses the arithmetic
    content from `omega_bit_cut_link`, not just extensionality. -/
theorem LR_bit_win_halts_equiv (Γ : Set OmegaSentence) (n a : ℕ) :
    Halts (LR_bit Γ n a) ↔ Halts (LR_win Γ n a) := by
  simp only [Halts]
  constructor
  · intro ⟨t, ht⟩
    exact ⟨t, (LR_bit_win_equiv Γ n a t).mp ht⟩
  · intro ⟨t, ht⟩
    exact ⟨t, (LR_bit_win_equiv Γ n a t).mpr ht⟩

/-- Rev equivalence for dual LR procedures (any kit). -/
theorem LR_bit_win_rev_equiv (K : RHKit) (Γ : Set OmegaSentence) (n a : ℕ) :
    Rev0_K K (LR_bit Γ n a) ↔ Rev0_K K (LR_win Γ n a) := by
  -- The traces are pointwise equivalent, hence propositionally equal
  have heq : LR_bit Γ n a = LR_win Γ n a := by
    funext t
    exact propext (LR_bit_win_equiv Γ n a t)
  rw [heq]

/-- **T1-Style Rev Equivalence**: Explicit that Rev depends only on Halts.

    This variant makes the RevHalt philosophy explicit:
    Rev0_K K tr ↔ Halts tr (via T1_traces), so if Halts(LR_bit) ↔ Halts(LR_win),
    then Rev(LR_bit) ↔ Rev(LR_win). -/
theorem LR_bit_win_rev_equiv_T1
    (K : RHKit) (hK : DetectsMonotone K) (Γ : Set OmegaSentence) (n a : ℕ) :
    Rev0_K K (LR_bit Γ n a) ↔ Rev0_K K (LR_win Γ n a) := by
  have hh : Halts (LR_bit Γ n a) ↔ Halts (LR_win Γ n a) :=
    LR_bit_win_halts_equiv Γ n a
  -- T1_traces : Rev0_K K tr ↔ Halts tr
  have h1 : Rev0_K K (LR_bit Γ n a) ↔ Halts (LR_bit Γ n a) := T1_traces K hK _
  have h2 : Rev0_K K (LR_win Γ n a) ↔ Halts (LR_win Γ n a) := T1_traces K hK _
  exact h1.trans (hh.trans h2.symm)

-- ==============================================================================================
-- 5. Semantic definitions for Ω (local, avoiding Unified dependency)
-- ==============================================================================================

/-- ModE for Ω. -/
def ModE_omega (Γ : Set OmegaSentence) : Set OmegaModel :=
  { M | ∀ φ ∈ Γ, OmegaSat M φ }

/-- ThE for Ω. -/
def ThE_omega (K : Set OmegaModel) : Set OmegaSentence :=
  { φ | ∀ M ∈ K, OmegaSat M φ }

/-- CloE for Ω. -/
def CloE_omega (Γ : Set OmegaSentence) : Set OmegaSentence :=
  ThE_omega (ModE_omega Γ)

/-- SemConsequences for Ω. -/
def SemConsequences_omega (Γ : Set OmegaSentence) (φ : OmegaSentence) : Prop :=
  φ ∈ CloE_omega Γ

/-- DynamicBridge for Ω. -/
def OmegaDynamicBridge : Prop :=
  ∀ Γ φ, SemConsequences_omega Γ φ ↔ Halts (LR_omega Γ φ)

-- ==============================================================================================
-- 6. DR0/DR1 for Ω
-- ==============================================================================================

/-- DR0 specialized to Ω. -/
theorem DR0_omega (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : OmegaDynamicBridge) :
    ∀ Γ φ, SemConsequences_omega Γ φ ↔ Rev0_K K (LR_omega Γ φ) := by
  intro Γ φ
  have h1 : SemConsequences_omega Γ φ ↔ Halts (LR_omega Γ φ) := hBridge Γ φ
  have h2 : Rev0_K K (LR_omega Γ φ) ↔ Halts (LR_omega Γ φ) := T1_traces K hK _
  exact h1.trans h2.symm

/-- DR1 specialized to Ω. -/
theorem DR1_omega
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, Rev0_K K₁ (LR_omega Γ φ) ↔ Rev0_K K₂ (LR_omega Γ φ) := by
  intro Γ φ
  have hL : Rev0_K K₁ (LR_omega Γ φ) ↔ Halts (LR_omega Γ φ) := T1_traces K₁ h₁ _
  have hR : Rev0_K K₂ (LR_omega Γ φ) ↔ Halts (LR_omega Γ φ) := T1_traces K₂ h₂ _
  exact hL.trans hR.symm

-- ==============================================================================================
-- 7. Key properties
-- ==============================================================================================

/-- Each bit verification eventually halts (if the bit stabilizes). -/
theorem omega_bit_halts (n : ℕ) (a : ℕ) :
    (∃ T, ∀ t ≥ T, (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = a) →
    Halts (LR_omega ∅ (OmegaSentence.BitIs n a)) := by
  intro ⟨T, hT⟩
  use T
  constructor
  · intro ψ hψ; exact False.elim (Set.notMem_empty ψ hψ)
  · simp only [OmegaSat]
    exact hT T (le_refl T)

-- Ω is not computable: no total function computes all bits.
-- This follows from classic uncomputability of halting (Rice's theorem).
-- The key insight is captured in section 9 CutComputable: we can attack Ω
-- via Cuts (semi-decidable) without needing to compute its Bits (undecidable).
--
-- theorem Omega_not_computable : ¬∃ (f : ℕ → ℕ), ∀ n, ∀ T,
--     (⌊(2 ^ n : ℕ) * OmegaApprox T⌋.toNat) % 2 = f n := by
--   sorry

-- ==============================================================================================
-- 8. Quanta-style packaging: Bit vs Win equivalence (Ω instance)
-- ==============================================================================================
/-!
## Overview

This section proves that `BitIs` and `WinDyad` — two syntactically orthogonal representations
of "the n-th bit of Ω is a" — have identical behavior at all levels:

1. **Sat-level (Hard Theorem)**: `omega_bit_win_sat_equiv`
   Pure arithmetic: the floor-based definition equals the dyadic window condition.
   This is the non-trivial content, derived from `omega_bit_cut_link`.

2. **SemConsequences-level**: `omega_bit_win_semConseq_equiv`
   Lifted from Sat-equivalence via standard model-theoretic reasoning.

3. **Rev-level (Immediate by Extensionality)**: `omega_bit_win_same_rev_verdict`
   Since `LR_omega` is extensional in `OmegaSat`, and Sat(BitIs) = Sat(WinDyad),
   the traces are equal, hence Rev verdicts are equal for any kit.
   No bridge hypothesis is needed at this level.
-/

namespace Quanta

open Set

-- ============================================================================
-- LEVEL 1: Sat-Equivalence (Hard Mathematical Theorem)
-- ============================================================================

/--
**Core Mathematical Result**: `BitIs` and `WinDyad` have identical satisfaction.

This is a pure arithmetic theorem about dyadic windows and floor functions.
The non-trivial content comes from `omega_bit_cut_link`.
-/
theorem omega_bit_win_sat_equiv (t : OmegaModel) (n a : ℕ) :
    OmegaSat t (OmegaSentence.BitIs n a) ↔ OmegaSat t (OmegaSentence.WinDyad n a) := by
  -- BitIs ↔ (∃k, Cut-window form) is omega_bit_cut_link (with x := ())
  have hBit :
      OmegaSat t (OmegaSentence.BitIs n a) ↔
      ∃ k : ℤ,
        OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) ()) ∧
        ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) ()) ∧
        k.toNat % 2 = a := by
    simpa [OmegaBit] using (omega_bit_cut_link (t := t) (n := n) (a := a) (x := ()))

  -- WinDyad ↔ same Cut-window form is omega_win_spec (with x := ())
  have hWin :
      OmegaSat t (OmegaSentence.WinDyad n a) ↔
      ∃ k : ℤ,
        OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) ()) ∧
        ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) ()) ∧
        k.toNat % 2 = a := by
    simpa [OmegaWin] using (omega_win_spec (t := t) (n := n) (a := a) (x := ()))

  exact hBit.trans hWin.symm

-- ============================================================================
-- LEVEL 2: Semantic Consequence Equivalence
-- ============================================================================

/--
**Semantic Consequence Equivalence**: Lifted from Sat-equivalence.

If φ and ψ are Sat-equivalent at every model, they have the same semantic consequences.
-/
theorem omega_bit_win_semConseq_equiv (Γ : Set OmegaSentence) (n a : ℕ) :
    SemConsequences_omega Γ (OmegaSentence.BitIs n a) ↔
    SemConsequences_omega Γ (OmegaSentence.WinDyad n a) := by
  simp only [SemConsequences_omega, CloE_omega, ThE_omega, ModE_omega, Set.mem_setOf_eq]
  constructor
  · intro hBit M hM
    rw [← omega_bit_win_sat_equiv]
    exact hBit M hM
  · intro hWin M hM
    rw [omega_bit_win_sat_equiv]
    exact hWin M hM

-- ============================================================================
-- LEVEL 3: Operative (Rev) Equivalence — Immediate by Extensionality
-- ============================================================================

/--
**Trace Equality**: `LR_omega` traces are propositionally equal for Bit vs Win.

Since `LR_omega Γ φ t = (∀ ψ ∈ Γ, OmegaSat t ψ) ∧ OmegaSat t φ`, and we proved
`OmegaSat t (BitIs n a) ↔ OmegaSat t (WinDyad n a)`, the traces are equal.
-/
theorem omega_bit_win_trace_equiv (Γ : Set OmegaSentence) (n a : ℕ) :
    LR_omega Γ (OmegaSentence.BitIs n a) = LR_omega Γ (OmegaSentence.WinDyad n a) := by
  funext t
  simp only [LR_omega]
  apply propext
  constructor
  · intro ⟨hΓ, hBit⟩
    exact ⟨hΓ, (omega_bit_win_sat_equiv t n a).mp hBit⟩
  · intro ⟨hΓ, hWin⟩
    exact ⟨hΓ, (omega_bit_win_sat_equiv t n a).mpr hWin⟩

/--
**Rev Equivalence (Unconditional)**: Same Rev verdict for Bit vs Win.

This follows immediately from trace equality — no kit validity or bridge hypothesis needed.
The result holds for **any** kit K.
-/
theorem omega_bit_win_same_rev_verdict (K : RHKit) :
    ∀ Γ (n a : ℕ),
      Rev0_K K (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
      Rev0_K K (LR_omega Γ (OmegaSentence.WinDyad n a)) := by
  intro Γ n a
  rw [omega_bit_win_trace_equiv]

/--
**Kit-Uniformity**: The equivalence holds for all kits simultaneously (trivial corollary).
-/
theorem omega_bit_win_same_rev_verdict_uniform (K₁ K₂ : RHKit) :
    ∀ Γ (n a : ℕ),
      (Rev0_K K₁ (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
       Rev0_K K₁ (LR_omega Γ (OmegaSentence.WinDyad n a))) ∧
      (Rev0_K K₂ (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
       Rev0_K K₂ (LR_omega Γ (OmegaSentence.WinDyad n a))) := by
  intro Γ n a
  exact ⟨omega_bit_win_same_rev_verdict K₁ Γ n a, omega_bit_win_same_rev_verdict K₂ Γ n a⟩

end Quanta

-- ==============================================================================================
-- 9. Computable Attack via Cuts (not Bits)
-- ==============================================================================================
/-!
## Key Insight: Attacking Ω Computably Without Determining Its Bits

The fundamental RevHalt insight for Ω is:

1. **Bits are NOT computable**: There is no algorithm that outputs the n-th bit of Ω.

2. **Cuts ARE semi-decidable**: For any q < Ω, we can eventually verify "Ω ≥ q" by running
   programs long enough until OmegaApprox t ≥ q.

3. **RevHalt leverages Cuts**: We can prove properties about Ω by examining the *halting*
   of traces that check Cuts, without ever computing individual bits.

This is the essence of the framework: we obtain computational verdicts about an incomputable
object by focusing on what IS computable (Cuts/halting) rather than what is NOT (Bits).
-/

namespace CutComputable

/-- **Cut traces halt when the cut is reached**.
    If Ω ≥ q (meaning some approximation reaches q), then the trace LR_omega ∅ (CutGe q) halts. -/
theorem omega_cut_halts_when_reached (q : ℚ) :
    (∃ t, OmegaApprox t ≥ q) → Halts (LR_omega ∅ (OmegaSentence.CutGe q)) := by
  intro ⟨t, ht⟩
  use t
  simp only [LR_omega, OmegaSat, Set.mem_empty_iff_false, forall_false, implies_true, true_and]
  exact ht

/-- **Converse: halting implies Ω ≥ q**.
    If the cut trace halts, then some approximation reached q. -/
theorem omega_cut_halts_iff_reached (q : ℚ) :
    Halts (LR_omega ∅ (OmegaSentence.CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q) := by
  constructor
  · intro ⟨t, ht⟩
    simp only [LR_omega, OmegaSat, Set.mem_empty_iff_false, forall_false, implies_true, true_and] at ht
    exact ⟨t, ht⟩
  · exact omega_cut_halts_when_reached q

/-- **RevHalt characterization of Cuts**.
    For any valid Kit, Rev0_K K (LR_omega ∅ (CutGe q)) ↔ ∃ t, OmegaApprox t ≥ q.

    This gives a COMPUTATIONAL characterization of "Ω ≥ q" via the Kit,
    even though Ω itself is not computable! -/
theorem omega_cut_rev_iff_reached (K : RHKit) (hK : DetectsMonotone K) (q : ℚ) :
    Rev0_K K (LR_omega ∅ (OmegaSentence.CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q) := by
  have hT1 : Rev0_K K (LR_omega ∅ (OmegaSentence.CutGe q)) ↔
             Halts (LR_omega ∅ (OmegaSentence.CutGe q)) := T1_traces K hK _
  exact hT1.trans (omega_cut_halts_iff_reached q)

/-- **Kit-invariance for Cut queries**.
    The answer to "Ω ≥ q?" is the same for any valid Kit. -/
theorem omega_cut_kit_invariant (K₁ K₂ : RHKit)
    (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) (q : ℚ) :
    Rev0_K K₁ (LR_omega ∅ (OmegaSentence.CutGe q)) ↔
    Rev0_K K₂ (LR_omega ∅ (OmegaSentence.CutGe q)) := by
  rw [omega_cut_rev_iff_reached K₁ h₁, omega_cut_rev_iff_reached K₂ h₂]

/-- **Monotonicity of Cut verdicts**.
    If we can verify "Ω ≥ q'" and q ≤ q', then we can verify "Ω ≥ q". -/
theorem omega_cut_verdict_mono (K : RHKit) (hK : DetectsMonotone K)
    {q q' : ℚ} (hle : q ≤ q') :
    Rev0_K K (LR_omega ∅ (OmegaSentence.CutGe q')) →
    Rev0_K K (LR_omega ∅ (OmegaSentence.CutGe q)) := by
  intro hRev
  rw [omega_cut_rev_iff_reached K hK] at hRev ⊢
  obtain ⟨t, ht⟩ := hRev
  exact ⟨t, le_trans hle ht⟩

/-- **Fundamental Asymmetry: Cuts are semi-decidable, Bits are not**.

    This theorem captures the key philosophical point:
    - The trace LR_omega ∅ (CutGe q) halts iff Ω ≥ q (semi-decidable: we can wait for it)
    - But the trace LR_omega ∅ (BitIs n a) may never halt if the bit is wrong

    We can "attack" Ω by asking cut questions, getting robust (Kit-invariant) answers,
    without ever needing to determine which specific bit values Ω has. -/
theorem cut_semidecidable_bit_not (n : ℕ) :
    -- For Cuts: halting characterizes reachability (semi-decidable)
    (∀ q, Halts (LR_omega ∅ (OmegaSentence.CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q)) ∧
    -- For Bits: halting only works if we guess the right bit
    (∀ a, Halts (LR_omega ∅ (OmegaSentence.BitIs n a)) →
          ∃ t, (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = a) := by
  constructor
  · exact omega_cut_halts_iff_reached
  · intro a hHalts
    obtain ⟨t, _, hSat⟩ := hHalts
    simp only [OmegaSat] at hSat
    exact ⟨t, hSat⟩

/-- **The Oracle Bridge for Ω works via Cuts**.

    The bridge `SemConsequences Γ φ ↔ Halts (LR Γ φ)` when specialized to Ω
    and Cut sentences gives us a computational semantics for rational comparisons.

    This is why Ω can be "understood" computationally even though its bits
    cannot be computed: we understand Ω through its Cut structure. -/
theorem omega_bridge_works_for_cuts (q : ℚ) (hBridge : OmegaDynamicBridge) :
    SemConsequences_omega ∅ (OmegaSentence.CutGe q) ↔ (∃ t, OmegaApprox t ≥ q) := by
  have h1 : SemConsequences_omega ∅ (OmegaSentence.CutGe q) ↔
            Halts (LR_omega ∅ (OmegaSentence.CutGe q)) := hBridge ∅ (OmegaSentence.CutGe q)
  exact h1.trans (omega_cut_halts_iff_reached q)

/-- **Enumeration of true Cuts**.
    The set of rationals q such that Ω ≥ q is recursively enumerable.
    We formalize this as: for each such q, the corresponding trace halts. -/
def TrueCuts : Set ℚ := { q | ∃ t, OmegaApprox t ≥ q }

theorem trueCuts_char (q : ℚ) :
    q ∈ TrueCuts ↔ Halts (LR_omega ∅ (OmegaSentence.CutGe q)) :=
  (omega_cut_halts_iff_reached q).symm

/-- **Negative results are NOT enumerable** (for Cuts above the true Ω).
    This is dual: if q > Ω (the limit), then LR_omega ∅ (CutGe q) never halts.
    We cannot computably enumerate "Ω < q" facts. -/
theorem false_cuts_dont_halt (q : ℚ) (hFalse : ∀ t, OmegaApprox t < q) :
    ¬Halts (LR_omega ∅ (OmegaSentence.CutGe q)) := by
  intro ⟨t, _, hSat⟩
  simp only [OmegaSat] at hSat
  have : OmegaApprox t < q := hFalse t
  exact not_le_of_gt this hSat

end CutComputable

end RevHalt.Dynamics.Instances.OmegaChaitin
