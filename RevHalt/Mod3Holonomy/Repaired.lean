/-
  RevHalt.Mod3Holonomy.Repaired

  Strict formalization of the Repaired System (Theorem 2 & 6).
  We implement the "Trivialization by Gauge" view.

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §8, §21
-/

import RevHalt.Mod3Holonomy.Groupoid
import Mathlib.Data.ZMod.Basic

namespace RevHalt.Mod3Holonomy

variable [Mod3Theory]

/-! ## 1. Repaired (Corrected) Transport (Basis Change)

We do not extend the state by a naive product bit; we perform a gauge/basis change
on primitive transports. The correction twists the transport itself by the unique
nontrivial involution (swap) according to φ(p).
This trivializes monodromy iff Flip = δφ.

T'_p(u) = T_p(u) - φ(p)  (Additive notation for: T' = τ^(-φ) ∘ T)
-/

/-- The corrected transport using a gauge φ (Basis Change) -/
def corrected_transport (φ : Gauge) (p : Path) (u : ZMod 2) : ZMod 2 :=
  u + transport p - φ p

/-! ## 2. Theorem 2: Repair Kills Holonomy (§8, §21)

Direction 1: If φ trivializes the flip, then the residual flip is 0.
-/

theorem repair_kills_flip (φ : Gauge)
    (h_gauge : ∀ α : TwoCell, α.getFlip = φ α.target - φ α.source) :
    ∀ α : TwoCell, α.getFlip - (φ α.target - φ α.source) = 0 := by
  intro α
  rw [h_gauge α]
  exact sub_self _

/-! ## 3. Theorem 6: Global Repair Equivalence (§21)

Direction 2 (Converse): If Repair is possible (Residual Flip is zero),
then the original Flip is a Cohoundary.
-/

theorem repair_implies_coboundary (φ : Gauge)
    (h_repair : ∀ α : TwoCell, α.getFlip - (φ α.target - φ α.source) = 0) :
    IsCoboundary := by
  use φ
  intro α
  have h := h_repair α
  -- Flip - (φ(tgt) - φ(src)) = 0 => Flip = φ(tgt) - φ(src)
  rw [sub_eq_zero] at h
  exact h

end RevHalt.Mod3Holonomy
