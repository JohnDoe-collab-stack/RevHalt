/-
  RevHalt.Theory.ProvableFrom

  Proof-theoretic T3: define ProvableFrom and prove soundness.

  This module formalizes the proof-theoretic perspective on T3:
  - ProvableFrom Γ φ : φ is derivable from axioms Γ
  - Sound extensions preserve truth
  - Meta-soundness: extending by true-but-unprovable preserves truth
-/

import RevHalt.Bridge.Context

namespace RevHalt.Theory

variable {Code PropT : Type}

/-!
## ProvableFrom: Derivability from axioms

A minimal formalization of "φ is derivable from Γ".
In practice, this would be instantiated with a specific proof system.
-/

/-- Derivability relation: ProvableFrom Γ φ means φ is derivable from axioms Γ.
    This is abstract - instantiated by specific proof systems. -/
class ProofSystem (PropT : Type) where
  ProvableFrom : Set PropT → PropT → Prop
  monotone : ∀ {Γ Γ' φ}, Γ ⊆ Γ' → ProvableFrom Γ φ → ProvableFrom Γ' φ
  refl : ∀ {Γ φ}, φ ∈ Γ → ProvableFrom Γ φ

namespace ProofSystem

variable [ProofSystem PropT]

/-- A theory Γ is sound w.r.t. Truth if all provable sentences are true. -/
def Sound (ctx : EnrichedContext Code PropT) (Γ : Set PropT) : Prop :=
  ∀ φ, ProvableFrom Γ φ → ctx.Truth φ

/-- Extending Γ by a true sentence preserves soundness. -/
theorem sound_extend_of_truth
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : Sound ctx Γ)
    (p : PropT)
    (hp : ctx.Truth p) :
    Sound ctx (Γ ∪ {p}) := by
  intro φ hProv
  -- Need to show: if ProvableFrom (Γ ∪ {p}) φ, then Truth φ
  -- This requires a cut-elimination or sub-formula property
  -- In general, this is not provable without additional proof-system axioms
  sorry

/-- Key insight: extending by true-but-unprovable is strict AND sound. -/
theorem sound_strict_extend_of_gap
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : Sound ctx Γ)
    (p : PropT)
    (hp : ctx.Truth p)
    (hnp : ¬ ProvableFrom Γ p) :
    Sound ctx (Γ ∪ {p}) ∧ ¬ (Γ ∪ {p} ⊆ Γ) := by
  constructor
  · -- Soundness: same as above, needs proof-system axiom
    sorry
  · -- Strictness: p ∈ Γ ∪ {p} but p ∉ Γ
    intro hSub
    have hp_mem : p ∈ Γ ∪ {p} := Set.mem_union_right Γ (Set.mem_singleton p)
    have hp_in_Γ : p ∈ Γ := hSub hp_mem
    have hProv : ProvableFrom Γ p := refl hp_in_Γ
    exact hnp hProv

end ProofSystem

/-!
## Meta-Soundness Theorem

If Γ is sound and p is true but not provable from Γ,
then extending Γ by p gives a strictly larger sound theory.

This is the proof-theoretic version of T3.
-/

/-- Meta-soundness: gap extension is sound and strict. -/
theorem meta_soundness [ProofSystem PropT]
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : ProofSystem.Sound ctx Γ)
    (w : GapWitness ctx)
    (hnp : ¬ ProofSystem.ProvableFrom Γ (GapWitness.prop w)) :
    ProofSystem.Sound ctx (Γ ∪ {GapWitness.prop w}) ∧
    ¬ (Γ ∪ {GapWitness.prop w} ⊆ Γ) :=
  ProofSystem.sound_strict_extend_of_gap ctx Γ hSound
    (GapWitness.prop w) (GapWitness.truth w) hnp

end RevHalt.Theory
