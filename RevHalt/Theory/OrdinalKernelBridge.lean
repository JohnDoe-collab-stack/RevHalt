import RevHalt.Base.Trace
import RevHalt.Theory.Stabilization

/-!
# RevHalt.Theory.OrdinalKernelBridge

This file provides the **explicit bridge** between:
- `Safe` (coinductive safety from transition systems)
- `Stabilizes` (Pi-1 property: ∀ n, ¬ T n)
- `up T = ⊥` (kernel-of-up form)

## The Key Insight

Any transition system `(Moves, Target)` induces a canonical trace `HitTrace x : ℕ → Prop`.
Then:
- `Safe Moves Target x` ↔ `Stabilizes (HitTrace Moves Target x)` ↔ `up (HitTrace x) = ⊥`

This unifies the coinductive (OrdinalCompression), logical (Stabilizes), and algebraic (kernel)
views of safety.
-/

namespace RevHalt.OrdinalKernelBridge

universe u
variable {X : Type u}

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Canonical Trace from Transition Systems
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Exactly-n-step reachability. -/
inductive ReachN (Moves : X → X → Prop) (x : X) : ℕ → X → Prop
  | zero : ReachN Moves x 0 x
  | succ {n y z} : ReachN Moves x n y → Moves y z → ReachN Moves x (n + 1) z

/-- The canonical "target-hit" trace: at time `n`, Target is reachable in exactly `n` steps. -/
def HitTrace (Moves : X → X → Prop) (Target : X → Prop) (x : X) : Trace :=
  fun n => ∃ y, ReachN Moves x n y ∧ Target y

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Coinductive Safety (Pure Relational)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reflexive-transitive reachability. -/
inductive Reachable (Moves : X → X → Prop) (x : X) : X → Prop
  | refl : Reachable Moves x x
  | step {y z} : Reachable Moves x y → Moves y z → Reachable Moves x z

/-- Safety: no reachable state hits Target. -/
def Safe (Moves : X → X → Prop) (Target : X → Prop) (x : X) : Prop :=
  ∀ y, Reachable Moves x y → ¬ Target y

/-- Safety operator (greatest fixpoint operator) in predicate form. -/
def G (Moves : X → X → Prop) (Target : X → Prop) (S : X → Prop) : X → Prop :=
  fun x => ¬ Target x ∧ ∀ y, Moves x y → S y

/-- Post-fixed point certificate: `C ⊆ G(C)` (predicate form). -/
def PostFix (Moves : X → X → Prop) (Target : X → Prop) (C : X → Prop) : Prop :=
  ∀ x, C x → G Moves Target C x

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) The Three Equivalences
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `ReachN` implies `Reachable`. -/
theorem reachable_of_reachN (Moves : X → X → Prop) (x : X) :
    ∀ n y, ReachN Moves x n y → Reachable Moves x y := by
  intro n y hn
  induction hn with
  | zero => exact Reachable.refl
  | succ _ hMove ih => exact Reachable.step ih hMove

/-- **Equivalence 1**: Safe ↔ Stabilizes(HitTrace). -/
theorem Safe_iff_Stabilizes_HitTrace (Moves : X → X → Prop) (Target : X → Prop) (x : X) :
    Safe Moves Target x ↔ Stabilizes (HitTrace Moves Target x) := by
  constructor
  · -- Safe → Stabilizes
    intro hSafe n hn
    rcases hn with ⟨y, hxy, hyT⟩
    have hR : Reachable Moves x y := reachable_of_reachN Moves x n y hxy
    exact hSafe y hR hyT
  · -- Stabilizes → Safe
    intro hStab y hReach hyT
    -- We need to show: ∃ n, HitTrace n, which would contradict hStab.
    -- First, show Reachable implies ∃ n, ReachN.
    suffices ∃ n, ReachN Moves x n y by
      obtain ⟨n, hn⟩ := this
      have hHit : HitTrace Moves Target x n := ⟨y, hn, hyT⟩
      exact hStab n hHit
    clear hyT hStab
    induction hReach with
    | refl => exact ⟨0, ReachN.zero⟩
    | step _ hMove ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, ReachN.succ hn hMove⟩

/-- **Equivalence 2**: Stabilizes(HitTrace) ↔ up(HitTrace) = ⊥. -/
theorem Stabilizes_HitTrace_iff_up_eq_bot (Moves : X → X → Prop) (Target : X → Prop) (x : X) :
    Stabilizes (HitTrace Moves Target x) ↔ up (HitTrace Moves Target x) = ⊥ :=
  Stabilizes_iff_up_eq_bot (HitTrace Moves Target x)

/-- **Master Equivalence**: Safe ↔ up(HitTrace) = ⊥. -/
theorem Safe_iff_up_eq_bot (Moves : X → X → Prop) (Target : X → Prop) (x : X) :
    Safe Moves Target x ↔ up (HitTrace Moves Target x) = ⊥ := by
  rw [Safe_iff_Stabilizes_HitTrace]
  exact Stabilizes_HitTrace_iff_up_eq_bot Moves Target x

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Coinduction Principle
-- ═══════════════════════════════════════════════════════════════════════════════

/-- PostFix implies invariance along all reachable states. -/
theorem postFix_imp_reachable_closed
    (Moves : X → X → Prop) (Target : X → Prop) (C : X → Prop)
    (hC : PostFix Moves Target C) (x : X) (hx : C x) :
    ∀ y, Reachable Moves x y → C y := by
  intro y hy
  induction hy with
  | refl => exact hx
  | step hReach hMove ih =>
      exact (hC _ ih).2 _ hMove

/-- **Coinduction**: PostFix C → C ⊆ Safe. -/
theorem postFix_imp_safe
    (Moves : X → X → Prop) (Target : X → Prop) (C : X → Prop)
    (hC : PostFix Moves Target C) (x : X) (hx : C x) :
    Safe Moves Target x := by
  intro y hy hyT
  have hyC : C y := postFix_imp_reachable_closed Moves Target C hC x hx y hy
  exact (hC y hyC).1 hyT

/-- **Coinduction (Kernel Form)**: PostFix C ∧ x ∈ C → up(HitTrace x) = ⊥. -/
theorem postFix_imp_up_eq_bot
    (Moves : X → X → Prop) (Target : X → Prop) (C : X → Prop)
    (hC : PostFix Moves Target C) (x : X) (hx : C x) :
    up (HitTrace Moves Target x) = ⊥ :=
  (Safe_iff_up_eq_bot Moves Target x).mp (postFix_imp_safe Moves Target C hC x hx)

end RevHalt.OrdinalKernelBridge

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.OrdinalKernelBridge.HitTrace
#print axioms RevHalt.OrdinalKernelBridge.Safe
#print axioms RevHalt.OrdinalKernelBridge.reachable_of_reachN
#print axioms RevHalt.OrdinalKernelBridge.Safe_iff_Stabilizes_HitTrace
#print axioms RevHalt.OrdinalKernelBridge.Stabilizes_HitTrace_iff_up_eq_bot
#print axioms RevHalt.OrdinalKernelBridge.Safe_iff_up_eq_bot
#print axioms RevHalt.OrdinalKernelBridge.postFix_imp_reachable_closed
#print axioms RevHalt.OrdinalKernelBridge.postFix_imp_safe
#print axioms RevHalt.OrdinalKernelBridge.postFix_imp_up_eq_bot
