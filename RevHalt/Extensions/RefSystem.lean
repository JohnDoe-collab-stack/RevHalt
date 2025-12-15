/-
# RevHalt.Extensions.RefSystem

Reference system layer: connecting `Cut` / `Bit` families to semantics and dynamics.

This module defines a minimal `RefSystem` interface compatible with the
RevHalt framework, to express the relation between continuous
(cut-based) and discrete (bit-based) encodings of a same referent `x : Referent`.

It provides:
* The structural typeclass `RefSystem`
* The compatibility axioms linking `Cut` and `Bit`
* A canonical kinetic local reading (`LR_ref`) producing a trace
* The bridge condition `DynamicBridge` specialized to this system
-/

import RevHalt.Theory
import Mathlib.Data.Rat.Floor

universe u v

namespace RevHalt

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

  /-- Antimonotonicity of Cut: if q ≤ q', then Sat M (Cut q' x) → Sat M (Cut q x).
      Interpretation: Cut q means "value ≥ q", so larger q is harder to satisfy. -/
  cut_antimono : ∀ {M q q' x}, q ≤ q' → Sat M (Cut q' x) → Sat M (Cut q x)

  /--
  Bit/Cut compatibility: for each bit position n and digit a,
  the truth of `Bit n a x` corresponds to a canonical dyadic window condition.
  To ensure arithmetic equivalence, we quantify over the integer index k.
  -/
  bit_cut_link :
    ∀ {M n a x},
      Sat M (Bit n a x) ↔
      ∃ (k : ℤ),
        Sat M (Cut ((k : ℚ) / (2 ^ n)) x) ∧
        ¬ Sat M (Cut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
        k.toNat % 2 = a

  /-- Win: dyadic window sentence (equivalent to Bit). -/
  Win : ℕ → ℕ → Referent → Sentence

  /-- Win specification: Win n a x ↔ same canonical dyadic RHS as bit_cut_link. -/
  win_spec :
    ∀ {M n a x},
      Sat M (Win n a x) ↔
      ∃ (k : ℤ),
        Sat M (Cut ((k : ℚ) / (2 ^ n)) x) ∧
        ¬ Sat M (Cut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
        k.toNat % 2 = a

namespace RefSystem

variable {Model : Type v} {Sentence : Type u} {Referent : Type*}
variable (E : RefSystem Model Sentence Referent)

/-!
## Kinetic Local Reading
We interpret a local reading LR Γ φ as a discrete-time trace expressing
progressive verification of φ under a reference system E.
-/
section InhabitedReferent
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
def CloK_ref (Γ : Set Sentence) : Set Sentence :=
  { φ | ∃ t, LR_ref E Γ φ t }

/-- Canonical Rev-based closure. -/
def CloRev_ref (K : RHKit) (Γ : Set Sentence) : Set Sentence :=
  { φ | Rev0_K K (LR_ref E Γ φ) }

end InhabitedReferent

/-!
## Semantic consequence for RefSystem (using E.Sat directly)
These definitions are purely semantic and don't require [Inhabited Referent].
-/

/-- ModE specialized to RefSystem. -/
def ModE_ref (Γ : Set Sentence) : Set Model := { M | ∀ φ ∈ Γ, E.Sat M φ }

/-- ThE specialized to RefSystem. -/
def ThE_ref (K_models : Set Model) : Set Sentence := { φ | ∀ M ∈ K_models, E.Sat M φ }

/-- CloE specialized to RefSystem. -/
def CloE_ref (Γ : Set Sentence) : Set Sentence := ThE_ref E (ModE_ref E Γ)

/-- SemConsequences specialized to RefSystem. -/
def SemConsequences_ref (Γ : Set Sentence) (φ : Sentence) : Prop := φ ∈ CloE_ref E Γ

/-!
## Bridge condition and DR0/DR1
These require [Inhabited Referent] because they use LR_ref.
-/
section InhabitedReferent
variable [Inhabited Referent]

/-- Bridge condition: semantic consequence matches halting of LR trace.
    Note: This is a strong hypothesis linking universal (semantic) to existential (halting). -/
def DynamicBridge_ref : Prop :=
  ∀ Γ φ, SemConsequences_ref E Γ φ ↔ Halts (LR_ref E Γ φ)

/-!
## Canonical theorems DR0 / DR1 specialized to RefSystem
-/

/-- DR0: semantic consequence ↔ kinetic verdict (via Rev). -/
theorem DR0_ref
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge_ref E) :
    ∀ Γ φ, SemConsequences_ref E Γ φ ↔ Rev0_K K (LR_ref E Γ φ) := by
  intro Γ φ
  have h1 : SemConsequences_ref E Γ φ ↔ Halts (LR_ref E Γ φ) := hBridge Γ φ
  have h2 : Rev0_K K (LR_ref E Γ φ) ↔ Halts (LR_ref E Γ φ) := T1_traces K hK _
  exact h1.trans h2.symm

/-- DR1: verdict is invariant across valid kits. -/
theorem DR1_ref
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂) :
    ∀ Γ φ, Rev0_K K₁ (LR_ref E Γ φ) ↔ Rev0_K K₂ (LR_ref E Γ φ) := by
  intro Γ φ
  have hL : Rev0_K K₁ (LR_ref E Γ φ) ↔ Halts (LR_ref E Γ φ) := T1_traces K₁ h₁ _
  have hR : Rev0_K K₂ (LR_ref E Γ φ) ↔ Halts (LR_ref E Γ φ) := T1_traces K₂ h₂ _
  exact hL.trans hR.symm

end InhabitedReferent

/-!
## Non-Trivial Equivalence: Bit ↔ Win (Semantic Level)

Two syntactically orthogonal sentences (Bit vs Win) have the same satisfaction.
These theorems don't require [Inhabited Referent].
-/

/-- Bit and Win have the same satisfaction (pointwise). -/
theorem bit_win_sat_equiv {M : Model} {n a : ℕ} {x : Referent} :
    E.Sat M (E.Bit n a x) ↔ E.Sat M (E.Win n a x) :=
  E.bit_cut_link.trans E.win_spec.symm

/-- Lifting lemma: Sat-equivalence implies SemConsequences-equivalence. -/
theorem sem_conseq_of_sat_equiv
    {φ ψ : Sentence} (h : ∀ M, E.Sat M φ ↔ E.Sat M ψ) :
    ∀ Γ, SemConsequences_ref E Γ φ ↔ SemConsequences_ref E Γ ψ := by
  intro Γ
  simp only [SemConsequences_ref, CloE_ref, ThE_ref, Set.mem_setOf_eq]
  constructor
  · intro hφ M hM
    rw [← h M]
    exact hφ M hM
  · intro hψ M hM
    rw [h M]
    exact hψ M hM

/-!
## Non-Trivial Equivalence: Bit ↔ Win (Operative Level)

These theorems require [Inhabited Referent] because they use LR_ref.
-/
section InhabitedReferent2
variable [Inhabited Referent]

/-- Bit and Win have the same Rev verdict (via DR0). -/
theorem bit_win_rev_equiv
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge_ref E) :
    ∀ Γ (n a : ℕ) (x : Referent),
      Rev0_K K (LR_ref E Γ (E.Bit n a x)) ↔ Rev0_K K (LR_ref E Γ (E.Win n a x)) := by
  intro Γ n a x
  have hSem : SemConsequences_ref E Γ (E.Bit n a x) ↔ SemConsequences_ref E Γ (E.Win n a x) :=
    sem_conseq_of_sat_equiv E (fun M => bit_win_sat_equiv E) Γ
  have hL := DR0_ref E K hK hBridge Γ (E.Bit n a x)
  have hR := DR0_ref E K hK hBridge Γ (E.Win n a x)
  exact hL.symm.trans (hSem.trans hR)

/-- Kit-invariance of Bit-Win equivalence (via DR1). -/
theorem bit_win_kit_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂)
    (hBridge : DynamicBridge_ref E) :
    ∀ Γ (n a : ℕ) (x : Referent),
      (Rev0_K K₁ (LR_ref E Γ (E.Bit n a x)) ↔ Rev0_K K₁ (LR_ref E Γ (E.Win n a x))) ∧
      (Rev0_K K₂ (LR_ref E Γ (E.Bit n a x)) ↔ Rev0_K K₂ (LR_ref E Γ (E.Win n a x))) := by
  intro Γ n a x
  exact ⟨bit_win_rev_equiv E K₁ h₁ hBridge Γ n a x, bit_win_rev_equiv E K₂ h₂ hBridge Γ n a x⟩

end InhabitedReferent2

end RefSystem

end RevHalt
