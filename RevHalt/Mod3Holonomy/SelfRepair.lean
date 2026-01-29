/-
  RevHalt.Mod3Holonomy.SelfRepair

  Self-regulation regimes (SR0, SR1) and the loop criterion

  Reference: docs/MOD3_HOLONOMIE_VERROUILLE.md §23-29, §32
-/

import RevHalt.Mod3Holonomy.Basic
import RevHalt.Mod3Holonomy.Cocycle
import RevHalt.Mod3Holonomy.Groupoid
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace RevHalt.Mod3Holonomy

/-! ## Self-Repair Regimes

(SR0) Strong: Flip ≡ 0 (flat)
(SR1) Structural: [Flip] = 0 in H¹ (trivializable by gauge)
-/

/-- (SR0) Strong self-regulation: all flips are zero -/
def StrongSelfRepair : Prop :=
  ∀ T₁ T₂ : Transport, flip T₁ T₂ = 0

/-- (SR1) Self-regulation: flip is a coboundary (uses Groupoid.IsCoboundary) -/
def SelfRepair : Prop := IsCoboundary

/-- Strong implies structural -/
theorem strong_implies_structural : StrongSelfRepair → SelfRepair := by
  intro h
  use fun _ => 0
  intro α
  simp only [TwoCell.getFlip, h α.source α.target, sub_self]

/-! ## Loop Criterion

SR1 ⟺ all loops have flip = 0

For our model where loops are identity 2-cells, this is automatic.
-/

/-- All identity cells have zero flip (Theorem C - trivial direction) -/
theorem loops_have_zero_flip : ∀ T : Transport, (TwoCell.id T).getFlip = 0 :=
  loop_flip_zero

/-! ## Confluence implies Self-Repair

If there exists a normal form N and all transports can be connected to N,
then we have a canonical gauge.
-/

/-- A normal form provides a canonical gauge -/
def normalFormGauge (N : Transport) (connect : Transport → Transport → ZMod 2) : Gauge :=
  fun T => connect T N

/-! ## ZMod 2 Helpers (Constructive) -/

lemma zmod2_neg (x : ZMod 2) : -x = x := by fin_cases x <;> decide
lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide
lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by rw [sub_eq_add_neg, zmod2_neg]

/-! ## Theorem C: SR1 ⟺ Loop-even

For any path-connected groupoid, SR1 holds we construct the gauge explicitly.
-/

/-- Theorem C: In our model, SR1 always holds -/
theorem selfRepair_holds : SelfRepair := by
  use fun T => flip T 1  -- gauge: flip to identity transport
  intro α
  simp only [TwoCell.getFlip]
  rw [zmod2_sub_eq_add, add_comm]
  -- Goal: flip S T = flip S 1 + flip T 1
  -- We know: flip S 1 = flip S T + flip T 1 (flip_additive)
  have h := flip_additive α.source α.target 1

  -- Add flip T 1 to both sides:
  -- flip S 1 + flip T 1 = (flip S T + flip T 1) + flip T 1
  have h_step1 : flip α.source 1 + flip α.target 1 = (flip α.source α.target + flip α.target 1) + flip α.target 1 := by
    rw [h]

  -- Re-associate: (flip S T + flip T 1) + flip T 1 = flip S T + (flip T 1 + flip T 1)
  have h_step2 : (flip α.source α.target + flip α.target 1) + flip α.target 1 = flip α.source α.target + (flip α.target 1 + flip α.target 1) := by
    exact add_assoc _ _ _

  -- Use reduction: flip T 1 + flip T 1 = 0
  have h_step3 : flip α.target 1 + flip α.target 1 = 0 := zmod2_add_self _

  -- Combine
  rw [h_step2, h_step3, add_zero] at h_step1
  exact h_step1.symm

/-- Normal form gauge trivializes the flip -/
theorem normalForm_trivializes (N : Transport) (connect : Transport → Transport → ZMod 2)
    (hconnect : ∀ T, connect T N = flip T N) :
    ∀ T₁ T₂ : Transport, flip T₁ T₂ = (normalFormGauge N connect) T₂ -
                                       (normalFormGauge N connect) T₁ := by
  intro T₁ T₂
  simp only [normalFormGauge, hconnect]
  rw [zmod2_sub_eq_add, add_comm]
  -- goal: flip T1 T2 = flip T1 N + flip T2 N
  -- know: flip T1 N = flip T1 T2 + flip T2 N
  have h := flip_additive T₁ T₂ N

  -- Add flip T2 N to both sides
  have h_step1 : flip T₁ N + flip T₂ N = (flip T₁ T₂ + flip T₂ N) + flip T₂ N := by
    rw [h]

  have h_step2 : (flip T₁ T₂ + flip T₂ N) + flip T₂ N = flip T₁ T₂ + (flip T₂ N + flip T₂ N) := by
    exact add_assoc _ _ _

  have h_step3 : flip T₂ N + flip T₂ N = 0 := zmod2_add_self _

  rw [h_step2, h_step3, add_zero] at h_step1
  exact h_step1.symm

end RevHalt.Mod3Holonomy
