/-
  RevHalt.Examples.BitWindowTheorem

  ═══════════════════════════════════════════════════════════════════════════════
  WHAT THIS DEMONSTRATES (Structure: Barrier / Separation)
  ═══════════════════════════════════════════════════════════════════════════════
  1. BIT ↔ WIN EQUIVALENCE: two syntactically different sentences, same truth.
  2. Bit = discrete digit assertion (non-computable to determine globally).
  3. Win = dyadic window via cuts (semi-decidable approximation).
  4. bit_cut_link bridges the discrete/continuous gap.
  5. Semantic equivalence: same satisfaction in all models.
  6. Rev equivalence: same verdict under any valid kit.
  7. Separates SYNTAX from SEMANTICS: orthogonal representations, same meaning.
  8. Simplifies Ω: bits are just boundaries between cut intervals.
  9. Pattern: two "readings" of the same referent → observationally identical.
  10. Key insight: cuts are the robust interface; bits are derived.
  ═══════════════════════════════════════════════════════════════════════════════
-/

import RevHalt.Dynamics.Core.RefSystem

namespace RevHalt.Examples

open RevHalt

/-!
## Bit ↔ Win Equivalence Demo

Bit and Win are syntactically different but semantically equivalent.
- Bit: discrete digit assertion
- Win: dyadic window condition (expressed via cuts)

The theorem `bit_win_sat_equiv` shows they have the same satisfaction.
The theorem `bit_win_rev_equiv` shows they have the same Rev verdict.
-/

variable {Model Sentence Referent : Type*}
variable (E : RefSystem Model Sentence Referent)

/-- Bit ↔ Win at the semantic level (pointwise satisfaction). -/
theorem bit_window_sat_equiv {M : Model} {n : ℕ} {a : Fin 2} {x : Referent} :
    E.Sat M (E.Bit n a x) ↔ E.Sat M (E.Win n a x) :=
  RefSystem.bit_win_sat_equiv E

/-- Bit ↔ Win at the closure level (semantic consequence). -/
theorem bit_window_sem_equiv (n : ℕ) (a : Fin 2) (x : Referent) (Γ : Set Sentence) :
    RefSystem.SemConsequences_ref E Γ (E.Bit n a x) ↔
    RefSystem.SemConsequences_ref E Γ (E.Win n a x) :=
  RefSystem.sem_conseq_of_sat_equiv E (fun _ => RefSystem.bit_win_sat_equiv E) Γ

/-!
## With Bridge: Bit ↔ Win at the Rev level

With the DynamicBridge hypothesis, Bit and Win have the same Rev verdict.
This demonstrates two operationally distinct "readings" (bit-based vs window-based)
that are observationally indistinguishable once routed through Rev.
-/

variable [Inhabited Referent]

/-- Bit ↔ Win at the Rev level (via DR0). -/
theorem bit_window_rev_equiv
    (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : RefSystem.DynamicBridge_ref E)
    (n : ℕ) (a : Fin 2) (x : Referent) (Γ : Set Sentence) :
    Rev0_K K (RefSystem.LR_ref E Γ (E.Bit n a x)) ↔
    Rev0_K K (RefSystem.LR_ref E Γ (E.Win n a x)) :=
  RefSystem.bit_win_rev_equiv E K hK hBridge Γ n a x

/-!
## Key point

This exemplifies the project's philosophy:
- Cuts are the semi-decidable interface (robust, kit-invariant)
- Bits are boundaries between cuts (non-computable but semantically equivalent to windows)
- Two distinct "readings" → same observable verdict
-/

end RevHalt.Examples
