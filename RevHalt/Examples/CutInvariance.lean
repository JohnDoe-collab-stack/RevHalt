/-
  RevHalt.Examples.CutInvariance

  ═══════════════════════════════════════════════════════════════════════════════
  WHAT THIS DEMONSTRATES (Structure: Rigidity)
  ═══════════════════════════════════════════════════════════════════════════════
  1. T1 RIGIDITY at RefSystem level: cuts are kit-invariant.
  2. Any two valid kits (DetectsMonotone) give the same Rev verdict on cuts.
  3. The verdict depends only on semantic consequence, not on the kit choice.
  4. DR1_ref: direct instantiation of closure rigidity for RefSystem.
  5. DR0_ref: semantic consequence ↔ Rev verdict (with DynamicBridge).
  6. Cuts (semi-decidable interface) are robust against kit variations.
  7. This simplifies existing results: no need to reason about specific kits.
  8. Pattern: closure C + agreement on C(X) ⇒ agreement on all X.
  9. Applicable to Ω cuts: same verdict regardless of observation method.
  10. Key insight: rigidity makes kit choice irrelevant for semantic queries.
  ═══════════════════════════════════════════════════════════════════════════════
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
