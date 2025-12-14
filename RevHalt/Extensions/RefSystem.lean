/-
# RevHalt.Extensions.RefSystem

Reference system layer: connecting `Cut` / `Bit` families to semantics and dynamics.

This module defines a minimal `RefSystem` interface compatible with the
`Closure.lean` framework, to express the relation between continuous
(cut-based) and discrete (bit-based) encodings of a same referent `x : Referent`.

It provides:
* The structural typeclass `RefSystem`
* The compatibility axioms linking `Cut` and `Bit`
* A canonical kinetic local reading (`LR_ref`) producing a trace
* The bridge condition `DynamicBridge` specialized to this system
-/

import RevHalt.Unified.Closure
import Mathlib.Data.Rat.Floor

universe u v

namespace RevHalt_Unified

open Set

/--
A *reference system* provides:
- a semantic relation `Sat` between models and sentences,
- two computable families of formulas:
  * `Cut q x` : comparison to a rational (continuous coordinate)
  * `Bit n a x` : value of a discrete digit (discrete coordinate)
and a compatibility law between them.
-/
structure RefSystem (Model : Type v) (Sentence : Type u) (Referent : Type*) where
  Sat : Model → Sentence → Prop
  Cut : ℚ → Referent → Sentence
  Bit : ℕ → ℕ → Referent → Sentence

  /-- Monotonicity of Cut: if q ≤ q', then Sat M (Cut q x) → Sat M (Cut q' x). -/
  cut_mono : ∀ {M q q' x}, q ≤ q' → Sat M (Cut q x) → Sat M (Cut q' x)

  /--
  Bit/Cut compatibility: for each bit position n and digit a,
  the truth of `Bit n a x` corresponds to a dyadic window condition
  on the cut values.
  -/
  bit_cut_link :
    ∀ {M n a x},
      Sat M (Bit n a x) ↔
      ∃ (q₀ q₁ : ℚ), q₁ - q₀ = (1 : ℚ) / (2 ^ n)
        ∧ Sat M (Cut q₀ x) ∧ ¬ Sat M (Cut q₁ x)
        ∧ (⌊(2 ^ n : ℕ) * q₀⌋.toNat) % 2 = a

namespace RefSystem

variable {Model : Type v} {Sentence : Type u} {Referent : Type*}
variable (E : RefSystem Model Sentence Referent)

/-!
## Kinetic Local Reading
We interpret a local reading LR Γ φ as a discrete-time trace expressing
progressive verification of φ under a reference system E.
-/

variable [Inhabited Referent]

/-- Local reading: at time t, we test all cuts and bits of depth ≤ t. -/
def LR_ref (Γ : Set Sentence) (φ : Sentence) : Trace :=
  fun t =>
    (∀ ψ ∈ Γ, ∃ M, E.Sat M ψ) ∧
    (∃ n ≤ t, φ = E.Bit n 1 default)  -- toy condition; in practice, bit-based refinement

/--
The kinetic closure induced by LR_ref:
`CloK_ref Γ` is the set of sentences that eventually stabilize true under LR_ref.
-/
def CloK_ref [Inhabited Referent] (Γ : Set Sentence) : Set Sentence :=
  { φ | ∃ t, LR_ref E Γ φ t }

/-- Canonical Rev-based closure. -/
def CloRev_ref [Inhabited Referent] (K : RHKit) (Γ : Set Sentence) : Set Sentence :=
  { φ | Rev0_K K (LR_ref E Γ φ) }

/-!
## Bridge condition
To align semantics (`Sat`) and dynamics (`LR_ref`), we require a bridge hypothesis:
for every Γ, φ, the semantic consequence matches halting of the LR trace.
-/
def DynamicBridge_ref [Inhabited Referent] : Prop :=
  ∀ Γ φ, SemConsequences E.Sat Γ φ ↔ Halts (LR_ref E Γ φ)

/-!
## Canonical theorems DR0 / DR1 specialized to RefSystem
These reuse the general theorems from Closure.lean
-/

/-- DR0: semantic consequence ↔ kinetic verdict (via Rev). -/
theorem DR0_ref
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge_ref E) :
    ∀ Γ φ, SemConsequences E.Sat Γ φ ↔ Rev0_K K (LR_ref E Γ φ) :=
  DR0_semantic_iff_verdict (Sat := E.Sat) (LR := LR_ref E) K hK hBridge

/-- DR1: verdict is invariant across valid kits. -/
theorem DR1_ref
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, Rev0_K K₁ (LR_ref E Γ φ) ↔ Rev0_K K₂ (LR_ref E Γ φ) := by
  intro Γ φ
  have hL : Rev0_K K₁ (LR_ref E Γ φ) ↔ Halts (LR_ref E Γ φ) := T1_traces K₁ h₁ _
  have hR : Rev0_K K₂ (LR_ref E Γ φ) ↔ Halts (LR_ref E Γ φ) := T1_traces K₂ h₂ _
  exact hL.trans hR.symm

end RefSystem

end RevHalt_Unified
