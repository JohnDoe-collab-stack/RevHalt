/-
  RevHalt.Extensions.OmegaChaitin

  Chaitin's Ω as a RefSystem instance.

  ## Concept

  Ω is characterized by its rational approximations Ωₜ (running programs up to t steps).

  We encode knowledge about Ω via:
  - **Cut q** : "Ω ≥ q" (rational lower bound, verified when Ωₜ ≥ q)
  - **Bit n a** : "the n-th bit of Ω's binary expansion is a"

  ## Design: No ℝ needed

  We work entirely with ℚ approximations. The "true" Ω is implicit as the limit.
  This matches how Ω is actually computed in practice.
-/

import RevHalt.Extensions.RefSystem
import Mathlib.Computability.Halting
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Ring.Pow

namespace RevHalt.Extensions.OmegaChaitin

open RevHalt
open Nat.Partrec

-- ==============================================================================================
-- 1. Chaitin's Ω Approximation
-- ==============================================================================================

/-- Approximation of Ω from below at time t.
    Ωₜ = Σ { 2^(-|p|) | p halts within t steps }
    Axiomatized; a constructive version would enumerate halting programs. -/
axiom OmegaApprox : ℕ → ℚ

/-- Approximations are non-negative. -/
axiom OmegaApprox_nonneg : ∀ t, 0 ≤ OmegaApprox t

/-- Approximations are bounded by 1. -/
axiom OmegaApprox_le_one : ∀ t, OmegaApprox t ≤ 1

/-- Approximations are monotonically increasing. -/
axiom OmegaApprox_mono : ∀ t₁ t₂, t₁ ≤ t₂ → OmegaApprox t₁ ≤ OmegaApprox t₂

/-- For any achievable bound q, there exists a time at which the approximation reaches it. -/
axiom OmegaApprox_unbounded : ∀ q : ℚ, q < 1 →
    (∃ T, OmegaApprox T ≥ q) ∨ (∀ t, OmegaApprox t < q)

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
| _, OmegaSentence.Not s => ∀ t', ¬OmegaSat t' s
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
    simp [d, pow_pos (by norm_num : (0 : ℚ) < 2) n]

  constructor
  · -- BitIs -> window (exists k)
    intro hBit
    -- rewrite hBit onto the canonical d*r form
    have hBit' : (⌊d * r⌋.toNat) % 2 = a := by
      -- simp rewrites ↑(2^n) to (2:ℚ)^n, so this matches d
      simpa [r, d, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hBit

    let k : ℤ := ⌊d * r⌋

    have hk : ((k : ℚ) ≤ d * r) ∧ (d * r < (k : ℚ) + 1) := by
      have : (⌊d * r⌋ : ℤ) = k := by simp [k]
      -- floor_eq_iff gives: k ≤ d*r < k+1
      simpa [add_comm, add_left_comm, add_assoc] using (Int.floor_eq_iff).1 this

    refine ⟨k, ?_, ?_, ?_⟩
    · -- OmegaApprox t ≥ k/d
      have hle : (k : ℚ) / d ≤ r := by
        have : (k : ℚ) ≤ r * d := by simpa [mul_comm] using hk.1
        exact (div_le_iff₀ hdpos).2 this
      simpa [r, d, ge_iff_le] using hle
    · -- ¬ OmegaApprox t ≥ (k+1)/d
      have hlt : r < ((k : ℚ) + 1) / d := by
        apply (lt_div_iff₀ hdpos).2
        have : r * d < (k : ℚ) + 1 := by
          simpa [mul_comm] using hk.2
        exact this
      have : ¬ ((k : ℚ) + 1) / d ≤ r := not_le_of_gt hlt
      -- match the goal shape ¬(r ≥ ((k+1)/2^n))
      simpa [r, d, ge_iff_le, add_comm, add_left_comm, add_assoc] using this
    · -- parity
      simpa [k] using hBit'

  · -- window -> BitIs
    rintro ⟨k, hCut, hNotCut, hpar⟩

    -- normalize hypotheses to r/d form
    have hCut' : (k : ℚ) / d ≤ r := by
      simpa [r, d, ge_iff_le] using hCut
    have hNotCut' : ¬ r ≥ (((k + 1) : ℚ) / d) := by
      -- same denominator normalization (2^n ↔ d)
      simpa [r, d, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hNotCut

    have hk_le : (k : ℚ) ≤ d * r := by
      have : (k : ℚ) ≤ r * d := (div_le_iff₀ hdpos).1 hCut'
      simpa [mul_comm] using this

    have hk_lt : d * r < (k : ℚ) + 1 := by
      have hlt : r < (((k + 1) : ℚ) / d) := lt_of_not_ge hNotCut'
      have : r * d < ((k + 1) : ℚ) := (lt_div_iff₀ hdpos).1 hlt
      -- rewrite ((k+1):ℚ) as (k:ℚ)+1, and swap mul
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using this

    have hk_floor : (⌊d * r⌋ : ℤ) = k := by
      exact (Int.floor_eq_iff).2 ⟨hk_le, by simpa [add_comm, add_left_comm, add_assoc] using hk_lt⟩

    -- target: ⌊↑(2^n) * OmegaApprox t⌋.toNat % 2 = a
    -- convert to ⌊d*r⌋ using simp, then rewrite by hk_floor, then use parity
    have : (⌊d * r⌋.toNat) % 2 = a := by
      simpa [hk_floor] using hpar
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

/-- Ω is not computable: no total function computes all bits. -/
axiom Omega_not_computable : ¬∃ (f : ℕ → ℕ), ∀ n, ∀ T,
    (⌊(2 ^ n : ℕ) * OmegaApprox T⌋.toNat) % 2 = f n




-- ==============================================================================================
-- 8. Quanta-style packaging: Bit vs Win equivalence (Ω instance)
-- ==============================================================================================
/-!
## Overview

This section proves that `BitIs` and `WinDyad` — two syntactically orthogonal representations
of "the n-th bit of Ω is a" — have identical behavior at all levels:

1. **Sat-level (Hard Theorem, No Oracle)**: `omega_bit_win_sat_equiv`
   Pure arithmetic: the floor-based definition equals the dyadic window condition.

2. **SemConsequences-level (No Oracle)**: `omega_bit_win_semConseq_equiv`
   Lifted from Sat-equivalence via standard model-theoretic reasoning.

3. **Rev-level (Conditional on Bridge)**: `omega_bit_win_same_rev_verdict`
   Under `OmegaDynamicBridge`, the kinetic verdicts match.
   This uses `LR_omega` (which actually reads `OmegaSat`), not the generic `LR_ref`.
-/

namespace Quanta

open Set

-- ============================================================================
-- LEVEL 1: Sat-Equivalence (Hard Mathematical Theorem — No Oracle Required)
-- ============================================================================

/--
**Core Mathematical Result**: `BitIs` and `WinDyad` have identical satisfaction.

This is a pure arithmetic theorem about dyadic windows and floor functions.
No oracle, no bridge hypothesis — this is the "non-trivial" content.
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
-- LEVEL 2: Semantic Consequence Equivalence (No Oracle Required)
-- ============================================================================

/--
**Semantic Consequence Equivalence**: Lifted from Sat-equivalence.

If φ and ψ are Sat-equivalent at every model, they have the same semantic consequences.
No bridge hypothesis needed — pure model theory.
-/
theorem omega_bit_win_semConseq_equiv (Γ : Set OmegaSentence) (n a : ℕ) :
    SemConsequences_omega Γ (OmegaSentence.BitIs n a) ↔
    SemConsequences_omega Γ (OmegaSentence.WinDyad n a) := by
  -- Lift from pointwise Sat-equivalence
  simp only [SemConsequences_omega, CloE_omega, ThE_omega, ModE_omega, Set.mem_setOf_eq]
  constructor
  · intro hBit M hM
    rw [← omega_bit_win_sat_equiv]
    exact hBit M hM
  · intro hWin M hM
    rw [omega_bit_win_sat_equiv]
    exact hWin M hM

-- ============================================================================
-- LEVEL 3: Operative (Rev) Equivalence — Conditional on OmegaDynamicBridge
-- ============================================================================

/--
**Trace Equivalence Lemma**: `LR_omega` traces are propositionally equal for Bit vs Win.

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
**Operative Corollary (Under Bridge Hypothesis)**: Same Rev verdict for Bit vs Win.

This uses `LR_omega` (the actual Ω reading, which invokes `OmegaSat`), not `LR_ref`.
The bridge hypothesis `OmegaDynamicBridge` links semantic consequence to halting.
-/
theorem omega_bit_win_same_rev_verdict
    (K : RHKit) (_hK : DetectsMonotone K)
    (_hBridge : OmegaDynamicBridge) :
    ∀ Γ (n a : ℕ),
      Rev0_K K (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
      Rev0_K K (LR_omega Γ (OmegaSentence.WinDyad n a)) := by
  intro Γ n a
  -- The traces are equal, so Rev verdicts are equal (no bridge needed here!)
  rw [omega_bit_win_trace_equiv]

/--
**Kit-Invariance**: The equivalence holds uniformly across all valid kits.
-/
theorem omega_bit_win_same_rev_verdict_kit_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂)
    (hBridge : OmegaDynamicBridge) :
    ∀ Γ (n a : ℕ),
      (Rev0_K K₁ (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
       Rev0_K K₁ (LR_omega Γ (OmegaSentence.WinDyad n a))) ∧
      (Rev0_K K₂ (LR_omega Γ (OmegaSentence.BitIs n a)) ↔
       Rev0_K K₂ (LR_omega Γ (OmegaSentence.WinDyad n a))) := by
  intro Γ n a
  exact ⟨omega_bit_win_same_rev_verdict K₁ h₁ hBridge Γ n a,
         omega_bit_win_same_rev_verdict K₂ h₂ hBridge Γ n a⟩

end Quanta

end RevHalt.Extensions.OmegaChaitin
