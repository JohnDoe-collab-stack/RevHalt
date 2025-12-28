/-
  RevHalt.Theory.ProvableFrom

  Proof-theoretic T3: define ProvableFrom and prove soundness.

  This module formalizes the proof-theoretic perspective on T3:
  - ProvableFrom Γ φ : φ is derivable from axioms Γ
  - Sound extensions preserve truth (requires rule-soundness axiom)
  - Meta-soundness: extending by a GapWitness is strict and preserves truth
-/

import RevHalt.Bridge.Context
import Mathlib.Data.Set.Basic

namespace RevHalt.Theory

open Set

variable {Code PropT : Type}

/-!
## ProofSystem: abstract derivability + semantic soundness

Without a soundness axiom relating ProvableFrom to Truth, one cannot prove that
extending a theory by a true axiom preserves truth of all derivations.
-/

class ProofSystem (PropT : Type) where
  /-- Derivability from axioms -/
  ProvableFrom : Set PropT → PropT → Prop
  /-- Monotonicity in the axiom set -/
  monotone : ∀ {Γ Γ' φ}, Γ ⊆ Γ' → ProvableFrom Γ φ → ProvableFrom Γ' φ
  /-- Axiom rule -/
  refl : ∀ {Γ φ}, φ ∈ Γ → ProvableFrom Γ φ
  /-- Semantic soundness schema: if all axioms are true, derivations are true -/
  soundness :
    ∀ {Code : Type} (ctx : EnrichedContext Code PropT) {Γ : Set PropT} {φ : PropT},
      (∀ p, p ∈ Γ → ctx.Truth p) →
      ProvableFrom Γ φ →
      ctx.Truth φ

namespace ProofSystem

variable [ProofSystem PropT]

/-- A theory Γ is sound (all derivable sentences are true). -/
def Sound (ctx : EnrichedContext Code PropT) (Γ : Set PropT) : Prop :=
  ∀ φ, ProvableFrom Γ φ → ctx.Truth φ

/-- If Γ is sound, then all axioms in Γ are true. -/
theorem axioms_true_of_sound
    (ctx : EnrichedContext Code PropT) (Γ : Set PropT)
    (hSound : Sound ctx Γ) :
    ∀ p, p ∈ Γ → ctx.Truth p := by
  intro p hp
  exact hSound p (ProofSystem.refl hp)

/-- Extending Γ by a true sentence preserves soundness. -/
theorem sound_extend_of_truth
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : Sound ctx Γ)
    (p : PropT)
    (hp : ctx.Truth p) :
    Sound ctx (Γ ∪ {p}) := by
  intro φ hProv
  have hAx : ∀ q, q ∈ (Γ ∪ {p}) → ctx.Truth q := by
    intro q hq
    rcases hq with hqΓ | hqp
    · -- q ∈ Γ
      exact (axioms_true_of_sound ctx Γ hSound) q hqΓ
    · -- q ∈ {p}
      have : q = p := by simpa [Set.mem_singleton_iff] using hqp
      simpa [this] using hp
  exact ProofSystem.soundness ctx hAx hProv

/-- Extending by a true-but-not-provable sentence is strict (and preserves soundness). -/
theorem sound_strict_extend_of_gap
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : Sound ctx Γ)
    (p : PropT)
    (hp : ctx.Truth p)
    (hnp : ¬ ProvableFrom Γ p) :
    Sound ctx (Γ ∪ {p}) ∧ ¬ (Γ ∪ {p} ⊆ Γ) := by
  constructor
  · exact sound_extend_of_truth ctx Γ hSound p hp
  · intro hSub
    have hp_mem : p ∈ (Γ ∪ {p}) := by
      exact Or.inr (by simp)
    have hp_in_Γ : p ∈ Γ := hSub hp_mem
    have hProv : ProvableFrom Γ p := ProofSystem.refl hp_in_Γ
    exact hnp hProv

end ProofSystem

/-!
## Meta-Soundness Theorem (proof-theoretic T3)

If Γ is sound and w is a GapWitness whose proposition is not derivable from Γ,
then Γ ∪ {w.prop} is sound and strictly extends Γ.
-/

theorem meta_soundness [ProofSystem PropT]
    (ctx : EnrichedContext Code PropT)
    (Γ : Set PropT)
    (hSound : ProofSystem.Sound (Code := Code) (PropT := PropT) ctx Γ)
    (w : GapWitness ctx)
    (hnp : ¬ ProofSystem.ProvableFrom (PropT := PropT) Γ (GapWitness.prop w)) :
    ProofSystem.Sound (Code := Code) (PropT := PropT) ctx (Γ ∪ {GapWitness.prop w}) ∧
    ¬ (Γ ∪ {GapWitness.prop w} ⊆ Γ) :=
  ProofSystem.sound_strict_extend_of_gap (Code := Code) (PropT := PropT)
    ctx Γ hSound (GapWitness.prop w) (GapWitness.truth w) hnp

end RevHalt.Theory
