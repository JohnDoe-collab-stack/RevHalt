import RevHalt.Theory.Complementarity
import RevHalt.Theory.Impossibility
import RevHalt.Theory.Stabilization

/-!
# RevHalt.Theory.QuantifierSwap

## The Quantifier Swap Principle

This file formalizes the key insight distinguishing T2 and T3:

- **T2 (Impossibility of Uniform Stabilization)**: ¬∃H ∀e (H total + correct + complete + r.e.)
  If we could uniformly detecting stabilization, we could decide halting.
- **T3 (Permissibility of Local Stabilization)**: ∀e ∃Sₑ ⊇ S₂ (Sₑ sound ∧ Sₑ determines e)
  The Kit allows us to extract a local *stabilization certificate* (`¬ Rev0_K`) for any specific `e`.

The "power" of RevHalt comes from this structural shift:
replacing the uniform demand `∃H ∀e` by the instancewise demand `∀e ∃Sₑ`,
where the extra power is the **Stabilization Certificate** extracted from the Kit.

## Main Results

- `T2_forbids_uniform`: No internal predicate can be uniformly total + correct
- `T3_permits_instancewise`: For each e, there exists a sound extension deciding e
- `quantifier_swap`: The two statements coexist without contradiction
-/

namespace RevHalt

open Nat.Partrec

/--
**Local Decision**: An extension Sₑ "decides" an encoded statement p
if it proves either p or its negation.
-/
def Decides {PropT : Type} (Provable : PropT → Prop) (Not : PropT → PropT) (p : PropT) : Prop :=
  Provable p ∨ Provable (Not p)

/--
**Sound Extension**: An extension is sound w.r.t. an external truth predicate
if every provable statement is true.
-/
def SoundExtension {PropT : Type}
    (Provable : PropT → Prop) (Truth : PropT → Prop) : Prop :=
  ∀ p, Provable p → Truth p

/--
**Instancewise Decision Witness**: For a given code e and oracle pick,
we can construct an extension that decides encode_halt(e).
-/
structure InstancewiseDecision {Code PropT : Type}
    (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code) where
  /-- The extension (represented as a set of sentences) -/
  S_e : Set PropT
  /-- S₂ is included -/
  extends_S2 : ∀ S2 : Set PropT, S2 ⊆ S_e
  /-- The chosen sentence is included -/
  has_pick : ∃ p, p ∈ S_e ∧
    ((Rev0_K S.K (S.Machine e) ∧ p = encode_halt e) ∨
     (¬ Rev0_K S.K (S.Machine e) ∧ p = encode_not_halt e))
  /-- Soundness -/
  sound : ∀ p ∈ S_e, Truth p

/--
**T3 permits instancewise decision**: Given an oracle pick for e,
we can construct a sound extension that "decides" encode_halt(e).

The key insight: for each e, there EXISTS an extension Sₑ that:
1. Is sound (preserves external truth)
2. Decides encode_halt(e) (proves either the positive or negative form)

This is the `∀e ∃Sₑ` form permitted by T3.
-/
theorem T3_permits_instancewise
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (e : Code)
    (pick : OraclePick S encode_halt encode_not_halt e) :
    ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧
      (∀ p ∈ S_e, Truth p) ∧
      (pick.p ∈ S_e) ∧
      ((pick.p = encode_halt e) ∨ (pick.p = encode_not_halt e)) := by
  -- Use the existing T3_oracle_extension_explicit
  -- The extension is S2 ∪ {pick.p}
  let S_e : Set PropT := S2 ∪ {pick.p}

  have hTruthPick : Truth pick.p := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        rw [hpEq]
        exact h_pos e hKit
    | inr h =>
        have hNotKit : KitStabilizes S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        rw [hpEq]
        exact h_neg e hNotKit

  have hPickForm : (pick.p = encode_halt e) ∨ (pick.p = encode_not_halt e) := by
    cases pick.cert with
    | inl h => exact Or.inl h.2
    | inr h => exact Or.inr h.2

  refine ⟨S_e, ?_, ?_, ?_, hPickForm⟩

  · -- S2 ⊆ S_e
    intro p hp
    exact Or.inl hp

  · -- Soundness
    intro p hp
    cases hp with
    | inl hp2 => exact h_S2_sound p hp2
    | inr hpick =>
        have hpEq : p = pick.p := hpick
        rw [hpEq]
        exact hTruthPick

  · -- pick.p ∈ S_e
    exact Or.inr rfl

/--
**The Quantifier Swap**: T2 and T3 coexist without contradiction.

- T2 says: ¬∃H ∀e (H total + correct + complete + r.e.)
- T3 says: ∀e ∃Sₑ (Sₑ sound + decides e) — given oracle picks

There is no contradiction because:
- T2 forbids a SINGLE internal predicate H that works for ALL e uniformly
- T3 allows DIFFERENT extensions Sₑ for EACH e individually

The power comes from external certification (oracle pick) that cannot be
globalized into an internal uniform decision procedure.
-/
theorem quantifier_swap_coexistence
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    -- T2: No uniform internal predicate
    (¬ ∃ _ : InternalHaltingPredicate S.toImpossibleSystem S.K, True) ∧
    -- T3: For each e, there exists a sound deciding extension
    (∀ e, ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧
      (∀ p ∈ S_e, Truth p) ∧
      ((picks e).p ∈ S_e)) := by
  constructor
  · -- T2 part: use T2_impossibility
    exact T2_impossibility S.toImpossibleSystem S.K S.h_canon
  · -- T3 part: use T3_permits_instancewise for each e
    intro e
    have h := T3_permits_instancewise S Truth S2 h_S2_sound
      encode_halt encode_not_halt h_pos h_neg e (picks e)
    obtain ⟨S_e, hSub, hSound, hMem, _⟩ := h
    exact ⟨S_e, hSub, hSound, hMem⟩

/-
**Summary of the Quantifier Swap**:

| Demand | Quantifier Form | Status | Interpretation |
|--------|-----------------|--------|----------------|
| Turing (uniform) | ∃H ∀e | Forbidden (T2) | No uniform Stabilization Detector |
| RevHalt (instancewise) | ∀e ∃Sₑ | Permitted (T3) | Local Stabilization Certificates |

The swap `∃H ∀e` → `∀e ∃Sₑ` is exactly the move from impossible uniform internal stability
to possible local external stability certification.
-/

end RevHalt
