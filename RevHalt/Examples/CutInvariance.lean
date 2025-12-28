/-
  RevHalt.Examples.CutInvariance

  Demonstration: cuts are kit-invariant under the RefSystem framework.
  This shows T1 rigidity at the RefSystem level.
-/

import RevHalt.Dynamics.Core.RefSystem

namespace RevHalt.Examples

open RevHalt

/-!
## Cut Invariance Demo

Cuts are kit-invariant: the Rev verdict on cut queries does not depend on
which valid kit is used, only on whether the semantic consequence holds.

This is a direct consequence of T1 (rigidity) applied to RefSystem.
-/

variable {Model Sentence Referent : Type*} [Inhabited Referent]
variable (E : RefSystem Model Sentence Referent)

/-- DR1 specialized to Cut queries: any two valid kits give the same verdict. -/
theorem cut_kit_invariance
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂)
    (q : ℚ) (x : Referent) (Γ : Set Sentence) :
    Rev0_K K₁ (RefSystem.LR_ref E Γ (E.Cut q x)) ↔
    Rev0_K K₂ (RefSystem.LR_ref E Γ (E.Cut q x)) :=
  RefSystem.DR1_ref E K₁ K₂ h₁ h₂ Γ (E.Cut q x)

/-- With the bridge hypothesis, semantic consequence ↔ Rev verdict ↔ Halts. -/
theorem cut_semantic_bridge
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : RefSystem.DynamicBridge_ref E)
    (q : ℚ) (x : Referent) (Γ : Set Sentence) :
    RefSystem.SemConsequences_ref E Γ (E.Cut q x) ↔
    Rev0_K K (RefSystem.LR_ref E Γ (E.Cut q x)) :=
  RefSystem.DR0_ref E K hK hBridge Γ (E.Cut q x)

/-!
## Key point

These theorems demonstrate:
1. Kit-invariance (DR1): the verdict doesn't depend on which valid kit we use
2. Semantic bridge (DR0): the verdict aligns with semantic consequence
3. This is T1 at the RefSystem level: "kits collapse to the same answer"
-/

end RevHalt.Examples
