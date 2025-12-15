/-
  RevHalt.Dynamics.Transport.Morphism

  TheoryMorphism: functorial transport between graphs.

  This is NOT a Move (internal operation).
  It's a functor between different axiom graphs.
-/

import RevHalt.Dynamics.Core.Path
import Mathlib.Data.Set.Basic

namespace RevHalt.Dynamics.Transport

open Set RevHalt

variable {Code₁ Code₂ PropT₁ PropT₂ : Type}

/-- A morphism between enriched contexts.
    Maps propositions while preserving truth and negation structure. -/
structure TheoryMorphism
    (ctx₁ : EnrichedContext Code₁ PropT₁)
    (ctx₂ : EnrichedContext Code₂ PropT₂) where
  /-- The map on propositions. -/
  map : PropT₁ → PropT₂
  /-- Preservation of truth. -/
  preserves_truth : ∀ p, ctx₁.Truth p → ctx₂.Truth (map p)
  /-- Preservation of negation structure. -/
  preserves_not : ∀ p, map (ctx₁.Not p) = ctx₂.Not (map p)

namespace TheoryMorphism

variable {ctx₁ : EnrichedContext Code₁ PropT₁}
variable {ctx₂ : EnrichedContext Code₂ PropT₂}

/-- Transport a theory (set of propositions). -/
def transport_theory (φ : TheoryMorphism ctx₁ ctx₂) (T : Set PropT₁) : Set PropT₂ :=
  image φ.map T

/-- Transport preserves soundness. -/
theorem transport_preserves_sound (φ : TheoryMorphism ctx₁ ctx₂)
    (T : Set PropT₁) (hT : TheorySound ctx₁ T) :
    TheorySound ctx₂ (transport_theory φ T) := by
  intro q hq
  simp only [transport_theory, mem_image] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact φ.preserves_truth p (hT p hp)

/-- Transport a theory node. -/
def transport_node (φ : TheoryMorphism ctx₁ ctx₂)
    (T : Dynamics.Core.TheoryNode ctx₁) : Dynamics.Core.TheoryNode ctx₂ where
  theory := transport_theory φ T.theory
  sound := transport_preserves_sound φ T.theory T.sound

/-- Transport preserves subset relation. -/
theorem transport_preserves_le (φ : TheoryMorphism ctx₁ ctx₂)
    (T₁ T₂ : Dynamics.Core.TheoryNode ctx₁) (h : T₁ ≤ T₂) :
    transport_node φ T₁ ≤ transport_node φ T₂ := by
  simp only [Dynamics.Core.TheoryNode.le_def, transport_node, transport_theory]
  exact Set.image_mono h

/-- Transport preserves strict subset (if map is injective on the theory). -/
theorem transport_preserves_lt (φ : TheoryMorphism ctx₁ ctx₂)
    (T₁ T₂ : Dynamics.Core.TheoryNode ctx₁) (h : T₁ < T₂)
    (hinj : Set.InjOn φ.map T₂.theory) :
    transport_node φ T₁ < transport_node φ T₂ := by
  simp only [Dynamics.Core.TheoryNode.lt_def] at h ⊢
  simp only [transport_node, transport_theory]
  -- Use Set.ssubset_iff_subset_ne
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · exact Set.image_mono h.subset
  · intro heq
    -- If images are equal and φ is injective on T₂, derive contradiction
    apply h.ne
    ext p
    constructor
    · intro hp
      exact h.subset hp
    · intro hp
      have hmem : φ.map p ∈ φ.map '' T₂.theory := Set.mem_image_of_mem φ.map hp
      rw [← heq] at hmem
      obtain ⟨q, hq, heq_map⟩ := hmem
      have hq2 : q ∈ T₂.theory := h.subset hq
      have heq_pq : q = p := hinj hq2 hp heq_map
      rw [← heq_pq]
      exact hq

end TheoryMorphism

end RevHalt.Dynamics.Transport
