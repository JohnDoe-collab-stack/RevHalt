import RevHalt.Theory.StructuralDichotomy
import RevHalt.Theory.AbstractDynamics

/-!
# SD_Bridge

The morphism from StructuralDichotomy oracles to AbstractDynamics PickWorld.

## Key Point


The oracle *contains* the side + proof; we just package it into a PickWorld.
This is the "parameterized dynamics" approach where the oracle is external.

## The Construction

`pickWorldOfSDOracle` takes:
- A structural dichotomy D
- An indexing function `elem : Index → X`
- An oracle `SDOracle D Index elem`

And produces a `PickWorld Index Prop` ready for AbstractDynamics.
-/

namespace RevHalt.StructuralDichotomy

open RevHalt.AbstractDynamics

variable {X : Type} [Preorder X] [Bot X] (D : StructuralDichotomy X)

/-- Turn an SDOracle into a PickWorld without any choice and without `noncomputable`. -/
def pickWorldOfSDOracle {Index : Type} (elem : Index → X)
    (oracle : SDOracle D Index elem) :
    AbstractDynamics.PickWorld Index Prop where
  Truth := fun P => P
  pick := fun i =>
    if (oracle i).side then D.Sig (elem i) else ¬ D.Sig (elem i)
  pick_true := by
    intro i
    cases hs : (oracle i).side with
    | false =>
        have hO : D.O (elem i) = ⊥ := by
          simpa [hs] using (oracle i).cert
        have hns : ¬ D.Sig (elem i) := (D.ker_iff (elem i)).1 hO
        simpa [hs] using hns
    | true =>
        have hS : D.Sig (elem i) := by
          simpa [hs] using (oracle i).cert
        simpa [hs] using hS

/-- The resulting PickWorld has Truth = id. -/
theorem pickWorldOfSDOracle_truth {Index : Type} (elem : Index → X)
    (oracle : SDOracle D Index elem) :
    (pickWorldOfSDOracle D elem oracle).Truth = id := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- Convenience: all AbstractDynamics machinery now available
-- ═══════════════════════════════════════════════════════════════════════════════

/-- State type for the derived PickWorld. -/
abbrev SDState {Index : Type} (elem : Index → X) (oracle : SDOracle D Index elem) :=
  (pickWorldOfSDOracle D elem oracle).State

/-- Chain for the derived PickWorld. -/
abbrev SDChain {Index : Type} (elem : Index → X) (oracle : SDOracle D Index elem)
    (S0 : SDState D elem oracle) (schedule : ℕ → Index) :=
  (pickWorldOfSDOracle D elem oracle).Chain S0 schedule

/-- Limit for the derived PickWorld. -/
abbrev SDLim {Index : Type} (elem : Index → X) (oracle : SDOracle D Index elem)
    (S0 : SDState D elem oracle) (schedule : ℕ → Index) :=
  AbstractDynamics.PickWorld.lim (fun n => (SDChain D elem oracle S0 schedule n).S)

/-- OmegaState for the derived PickWorld. -/
abbrev SDOmegaState {Index : Type} (elem : Index → X) (oracle : SDOracle D Index elem)
    (S0 : SDState D elem oracle) :=
  (pickWorldOfSDOracle D elem oracle).omegaState S0

-- ═══════════════════════════════════════════════════════════════════════════════
-- Key Theorem: All abstract results apply
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Schedule invariance for SD dynamics. -/
theorem sd_lim_eq_of_fair_schedules {Index : Type} (elem : Index → X)
    (oracle : SDOracle D Index elem) (S0 : SDState D elem oracle)
    (schedule₁ schedule₂ : ℕ → Index)
    (hFair₁ : AbstractDynamics.PickWorld.Fair schedule₁)
    (hFair₂ : AbstractDynamics.PickWorld.Fair schedule₂) :
    SDLim D elem oracle S0 schedule₁ = SDLim D elem oracle S0 schedule₂ :=
  (pickWorldOfSDOracle D elem oracle).lim_eq_of_fair_schedules S0 schedule₁ schedule₂ hFair₁ hFair₂

/-- Limit equals omegaState under fair schedule. -/
theorem sd_lim_eq_omegaState {Index : Type} (elem : Index → X)
    (oracle : SDOracle D Index elem) (S0 : SDState D elem oracle)
    (schedule : ℕ → Index)
    (hFair : AbstractDynamics.PickWorld.Fair schedule) :
    SDLim D elem oracle S0 schedule = (SDOmegaState D elem oracle S0).S :=
  (pickWorldOfSDOracle D elem oracle).lim_eq_omegaState S0 schedule hFair

end RevHalt.StructuralDichotomy

-- Axiom checks (auto):
#print axioms RevHalt.StructuralDichotomy.pickWorldOfSDOracle_truth
#print axioms RevHalt.StructuralDichotomy.sd_lim_eq_of_fair_schedules
#print axioms RevHalt.StructuralDichotomy.sd_lim_eq_omegaState
