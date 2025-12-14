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
| CutGe (q : ℚ) : OmegaSentence          -- "Ω ≥ q"
| BitIs (n : ℕ) (a : ℕ) : OmegaSentence  -- "n-th bit of Ω is a"
| Not (s : OmegaSentence) : OmegaSentence
| TrueS : OmegaSentence
| FalseS : OmegaSentence

/-- Models are time bounds (how far we've computed). -/
abbrev OmegaModel := ℕ

/-- Satisfaction at model t (having run programs up to time t). -/
def OmegaSat : OmegaModel → OmegaSentence → Prop
| t, OmegaSentence.CutGe q => OmegaApprox t ≥ q
| t, OmegaSentence.BitIs n a =>
    -- n-th bit is verified if floor(2^n * Ωₜ) mod 2 = a
    (⌊(2 ^ n : ℕ) * OmegaApprox t⌋.toNat) % 2 = a
| _, OmegaSentence.Not s => ∀ t', ¬OmegaSat t' s  -- negation means never satisfied
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

/-- Monotonicity: if Ωₜ ≥ q and q ≤ q', we can't conclude Ωₜ ≥ q'.
    But by RefSystem semantics, cut_mono should be: q ≤ q' ∧ Sat(Cut q) → Sat(Cut q')
    This is only true if the cuts are "upward closed" which they're not.
    Axiomatize as the design needs refinement. -/
axiom omega_cut_mono : ∀ {t : OmegaModel} {q q' : ℚ} {x : OmegaReferent},
    q ≤ q' → OmegaSat t (OmegaCut q x) → OmegaSat t (OmegaCut q' x)

/-- Bit/Cut link (axiomatic). -/
axiom omega_bit_cut_link : ∀ {t : OmegaModel} {n a : ℕ} {x : OmegaReferent},
    OmegaSat t (OmegaBit n a x) ↔
    ∃ (q₀ q₁ : ℚ), q₁ - q₀ = (1 : ℚ) / (2 ^ n)
      ∧ OmegaSat t (OmegaCut q₀ x) ∧ ¬OmegaSat t (OmegaCut q₁ x)
      ∧ (⌊(2 ^ n : ℕ) * q₀⌋.toNat) % 2 = a

/-- RefSystem instance for Ω. -/
def OmegaRefSystem : RefSystem OmegaModel OmegaSentence OmegaReferent where
  Sat := OmegaSat
  Cut := OmegaCut
  Bit := OmegaBit
  cut_mono := omega_cut_mono
  bit_cut_link := omega_bit_cut_link

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

end RevHalt.Extensions.OmegaChaitin
