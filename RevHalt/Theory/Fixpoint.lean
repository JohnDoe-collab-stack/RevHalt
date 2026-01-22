import RevHalt.Theory.TheoryDynamics

/-!
# RevHalt.Theory.Fixpoint

This module formalizes the fundamental characterization of operational fixpoints
in terms of frontier nullity.

## Main Result

Under absorption, a theory state is a fixpoint of the minimal step operator F0
if and only if its frontier is empty:

  `F0 Γ = Γ ↔ S1Rel Γ = ∅`  (under Absorbable Γ)

This makes the Bulk/Frontier separation non-philosophical:
a theory is a fixpoint of the step operator exactly when its frontier is empty.

## Conceptual Significance

This theorem clarifies the gap between:
- **Existential fixpoints (Tarski)**: guaranteed by lattice theory
- **Iterative fixpoints (Kleene)**: require frontier extinction

The frontier is the engine of growth. When it vanishes, iteration stops.
When it persists, growth continues indefinitely.
-/

namespace RevHalt

open Set

universe u

variable {PropT : Type u}
variable {Code : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/-! ## Core Fixpoint Characterization -/

/--
  **Frontier Nullity implies Fixpoint** (unconditional direction).
  No absorption hypothesis needed for this direction.
-/
theorem F0_eq_self_of_S1Rel_empty
    (Γ : Set PropT)
    (hEmpty : S1Rel Provable K Machine encode_halt Γ = ∅) :
    F0 Provable K Machine encode_halt Γ = Γ := by
  simp only [F0, hEmpty, union_empty]

/--
  **Fixpoint Characterization under Absorption**:
  If Γ is absorbable, then F0(Γ) = Γ if and only if S1Rel(Γ) = ∅.

  This is the fundamental equivalence:
  - Forward: If F0(Γ) = Γ, then Γ ∪ S1Rel(Γ) = Γ, so S1Rel(Γ) ⊆ Γ.
    But any p ∈ S1Rel(Γ) has ¬Provable Γ p, while Absorbable gives
    p ∈ Γ → Provable Γ p. Contradiction.
  - Backward: If S1Rel(Γ) = ∅, then F0(Γ) = Γ ∪ ∅ = Γ.
-/
theorem F0_eq_self_iff_S1Rel_empty
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ) :
    F0 Provable K Machine encode_halt Γ = Γ ↔
    S1Rel Provable K Machine encode_halt Γ = ∅ := by
  constructor
  · -- Forward: F0(Γ) = Γ → S1Rel(Γ) = ∅
    intro hFix
    by_contra hNe
    rw [← ne_eq, ← nonempty_iff_ne_empty] at hNe
    obtain ⟨p, hp⟩ := hNe
    -- p ∈ S1Rel(Γ) means p = encode_halt e, Kit(e), ¬Provable Γ p
    obtain ⟨e, hpEq, hKit, hNprov⟩ := hp
    -- Reconstruct S1Rel membership
    have hp' : p ∈ S1Rel Provable K Machine encode_halt Γ := ⟨e, hpEq, hKit, hNprov⟩
    -- p ∈ F0(Γ) = Γ ∪ S1Rel(Γ) via right side
    have hMemF0 : p ∈ F0 Provable K Machine encode_halt Γ := Or.inr hp'
    -- F0(Γ) = Γ, so p ∈ Γ
    rw [hFix] at hMemF0
    -- Absorbable: p ∈ Γ → Provable Γ p
    have hProv : Provable Γ p := hAbs p hMemF0
    -- Contradiction with ¬Provable Γ p
    rw [hpEq] at hProv
    exact hNprov hProv
  · -- Backward: S1Rel(Γ) = ∅ → F0(Γ) = Γ
    exact F0_eq_self_of_S1Rel_empty Provable K Machine encode_halt Γ

/--
  **Fixpoint implies Frontier Nullity under Absorption**.
  Absorption is necessary for this direction.
-/
theorem S1Rel_empty_of_F0_eq_self
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ)
    (hFix : F0 Provable K Machine encode_halt Γ = Γ) :
    S1Rel Provable K Machine encode_halt Γ = ∅ :=
  (F0_eq_self_iff_S1Rel_empty Provable K Machine encode_halt Γ hAbs).mp hFix

/--
  **Corollary**: Under absorption, Γ is NOT a fixpoint of F0 iff S1Rel(Γ) ≠ ∅.
-/
theorem F0_ne_self_iff_S1Rel_nonempty
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ) :
    F0 Provable K Machine encode_halt Γ ≠ Γ ↔
    (S1Rel Provable K Machine encode_halt Γ).Nonempty := by
  constructor
  · -- Forward: F0(Γ) ≠ Γ → S1Rel(Γ).Nonempty
    intro hNe
    by_contra hEmpty
    rw [nonempty_iff_ne_empty, not_not] at hEmpty
    have hFix := F0_eq_self_of_S1Rel_empty Provable K Machine encode_halt Γ hEmpty
    exact hNe hFix
  · -- Backward: S1Rel(Γ).Nonempty → F0(Γ) ≠ Γ
    intro ⟨p, hp⟩ hFix
    have hEmpty := S1Rel_empty_of_F0_eq_self Provable K Machine encode_halt Γ hAbs hFix
    rw [hEmpty] at hp
    exact hp

/-! ## Extension to Full Step F -/

/--
  **Full Step Fixpoint Characterization**:
  Under absorption and Cn extensive, F(Γ) = Γ implies S1Rel(Γ) = ∅.

  (The converse requires Cn Γ = Γ, which is the Cn-closed hypothesis.)
-/
theorem S1Rel_empty_of_F_eq_self
    (Cn : Set PropT → Set PropT)
    (hCnExt : CnExtensive Cn)
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ)
    (hFix : F Provable K Machine encode_halt Cn Γ = Γ) :
    S1Rel Provable K Machine encode_halt Γ = ∅ := by
  by_contra hNe
  rw [← ne_eq, ← nonempty_iff_ne_empty] at hNe
  obtain ⟨p, hp⟩ := hNe
  obtain ⟨e, hpEq, hKit, hNprov⟩ := hp
  -- Reconstruct the S1Rel membership for later use
  have hp' : p ∈ S1Rel Provable K Machine encode_halt Γ := ⟨e, hpEq, hKit, hNprov⟩
  -- p ∈ S1Rel(Γ) ⊆ Γ ∪ S1Rel(Γ) ⊆ Cn(Γ ∪ S1Rel(Γ)) = F(Γ) = Γ
  have hUnion : p ∈ Γ ∪ S1Rel Provable K Machine encode_halt Γ := Or.inr hp'
  have hCn : p ∈ Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := hCnExt _ hUnion
  have hF : p ∈ F Provable K Machine encode_halt Cn Γ := hCn
  rw [hFix] at hF
  have hProv : Provable Γ p := hAbs p hF
  rw [hpEq] at hProv
  exact hNprov hProv

/--
  **Full Step Fixpoint under Cn-closed**:
  If Cn Γ = Γ, then F(Γ) = Γ iff S1Rel(Γ) = ∅.
-/
theorem F_eq_self_iff_S1Rel_empty
    (Cn : Set PropT → Set PropT)
    (hCnExt : CnExtensive Cn)
    (Γ : Set PropT)
    (hCnClosed : Cn Γ = Γ)
    (hAbs : Absorbable Provable Γ) :
    F Provable K Machine encode_halt Cn Γ = Γ ↔
    S1Rel Provable K Machine encode_halt Γ = ∅ := by
  constructor
  · exact S1Rel_empty_of_F_eq_self Provable K Machine encode_halt Cn hCnExt Γ hAbs
  · intro hEmpty
    -- F(Γ) = Cn(Γ ∪ S1Rel(Γ)) = Cn(Γ ∪ ∅) = Cn(Γ) = Γ
    simp only [F, hEmpty, union_empty, hCnClosed]

/-! ## Headline Corollary: Open System Cannot Be a Fixpoint -/

/--
  **Open System Excludes Fixpoint**:
  Under absorption, if the frontier is nonempty (RouteIIAt), then F0 is not a fixpoint.

  This is the core operational statement:
  - Absorbable = membership implies provability
  - RouteIIAt = frontier nonempty = system is "open"
  - Together they exclude F0 Γ = Γ.
-/
theorem F0_ne_self_of_absorbable_and_RouteIIAt
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ)
    (hRoute : RouteIIAt Provable K Machine encode_halt Γ) :
    F0 Provable K Machine encode_halt Γ ≠ Γ :=
  (F0_ne_self_iff_S1Rel_nonempty Provable K Machine encode_halt Γ hAbs).mpr hRoute

/--
  **Alternative formulation (forall version)**:
  Frontier nullity without set equality, using universal quantification.
  This avoids the `Nonempty ↔ ≠ ∅` equivalence.
-/
theorem F0_eq_self_iff_forall_not_mem_S1Rel
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ) :
    F0 Provable K Machine encode_halt Γ = Γ ↔
    (∀ p, p ∉ S1Rel Provable K Machine encode_halt Γ) := by
  rw [F0_eq_self_iff_S1Rel_empty Provable K Machine encode_halt Γ hAbs]
  constructor
  · intro hEmpty p hp
    rw [hEmpty] at hp
    exact hp
  · intro hForall
    exact eq_empty_of_forall_notMem hForall

end RevHalt
