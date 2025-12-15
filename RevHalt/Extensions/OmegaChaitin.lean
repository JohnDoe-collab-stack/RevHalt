/-
  RevHalt.Extensions.OmegaChaitin

  "Vrai" Ω : aucune axiomatisation de `OmegaApprox`.
  On définit une approximation rationnelle par somme finie sur les codes < t
  qui terminent dans `evaln t`.

  Remarque : ce Ω est une halting-probability (poids 2^-(p+1)) d'une machine
  prefix-free via un codage unaire implicite des programmes (index p ↦ longueur p+1).
-/

import RevHalt.Extensions.RefSystem
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset

namespace RevHalt.Extensions.OmegaChaitin

open RevHalt
open Nat.Partrec
open Classical

-- ==============================================================================================
-- 1. "Vrai" Ω Approximation (no axioms - fully constructive)
-- ==============================================================================================

/-- Weight of program index `p` (dyadic). -/
def omegaWeight (p : ℕ) : ℚ := (1 : ℚ) / ((2 : ℚ) ^ (p + 1))

/-- `haltsWithin t p n` : the decoded Partrec code `p` returns some value on input `n`
    within the `evaln t` search bound. -/
def haltsWithin (t p n : ℕ) : Prop :=
  ∃ x : ℕ, x ∈ (Nat.Partrec.Code.ofNatCode p).evaln t n

/-- Monotonicity of `haltsWithin` in the bound `t`. -/
theorem haltsWithin_mono {t₁ t₂ p n : ℕ} (h : t₁ ≤ t₂) :
    haltsWithin t₁ p n → haltsWithin t₂ p n := by
  rintro ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Nat.Partrec.Code.evaln_mono h hx

/-- Finite approximation Ωₜ (rational). -/
noncomputable def OmegaApprox (t : ℕ) : ℚ :=
  ∑ p ∈ Finset.range t,
    (if haltsWithin t p 0 then omegaWeight p else 0)

/-- Approximations are non-negative. -/
theorem OmegaApprox_nonneg : ∀ t, 0 ≤ OmegaApprox t := by
  intro t
  classical
  unfold OmegaApprox
  apply Finset.sum_nonneg
  intro p _
  by_cases hH : haltsWithin t p 0
  · simp only [if_pos hH, omegaWeight]
    apply div_nonneg
    · norm_num
    · apply pow_nonneg; norm_num
  · simp only [if_neg hH, le_refl]

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
  classical
  have h_le_sumWeights :
      OmegaApprox t ≤ ∑ p ∈ Finset.range t, omegaWeight p := by
    unfold OmegaApprox
    apply Finset.sum_le_sum
    intro p _
    by_cases hH : haltsWithin t p 0
    · simp only [if_pos hH, le_refl]
    · simp only [if_neg hH, omegaWeight]
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
  classical
  have h_termwise :
      (∑ p ∈ Finset.range t₁,
        (if haltsWithin t₁ p 0 then omegaWeight p else 0))
      ≤
      (∑ p ∈ Finset.range t₁,
        (if haltsWithin t₂ p 0 then omegaWeight p else 0)) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hH : haltsWithin t₁ p 0
    · have hH' : haltsWithin t₂ p 0 := haltsWithin_mono h12 hH
      simp only [if_pos hH, if_pos hH', le_refl]
    · by_cases hH' : haltsWithin t₂ p 0
      · simp only [if_neg hH, if_pos hH', omegaWeight]
        apply div_nonneg
        · norm_num
        · apply pow_nonneg; norm_num
      · simp only [if_neg hH, if_neg hH', le_refl]
  have h_extend :
      (∑ p ∈ Finset.range t₁,
        (if haltsWithin t₂ p 0 then omegaWeight p else 0))
      ≤
      (∑ p ∈ Finset.range t₂,
        (if haltsWithin t₂ p 0 then omegaWeight p else 0)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hp) h12)
    · intro p _ _
      by_cases hH : haltsWithin t₂ p 0
      · simp only [if_pos hH, omegaWeight]
        apply div_nonneg
        · norm_num
        · apply pow_nonneg; norm_num
      · simp only [if_neg hH, le_refl]
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

/-- Ω is not computable: no total function computes all bits.
    This follows from classic uncomputability of halting, but we state it as a theorem
    (it could be proven from Rice's theorem in Mathlib). -/
theorem Omega_not_computable : ¬∃ (f : ℕ → ℕ), ∀ n, ∀ T,
    (⌊(2 ^ n : ℕ) * OmegaApprox T⌋.toNat) % 2 = f n := by
  -- This would require connecting to uncomputability results in Mathlib
  -- For now, we note that if such f existed, we could decide halting
  intro ⟨f, hf⟩
  -- The proof would proceed by showing f decides halting, contradicting Rice's theorem
  -- This is left as sorry for now, but the statement is classically true
  sorry

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

end RevHalt.Extensions.OmegaChaitin
