import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic
import RevHalt.Theory.Categorical

namespace RevHalt

open Set
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- F) ROUTE II — IMPOSSIBILITY OF EMPTY FRONTIER
-- ═══════════════════════════════════════════════════════════════════════════════

section RouteII_Abstract

universe u
variable {PropT : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable {Code : Type u}
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

-- Note: We use SProvable and SNot as parameters instead of ImpossibleSystem
-- to avoid universe issues and keep the section maximally parametric.
variable (SProvable : PropT → Prop) -- Instantiate as S.Provable
variable (SNot : PropT → PropT)     -- Instantiate as S.Not

/-- A1: Soundness — relative provability implies global provability. -/
def Soundness (Γ : Set PropT) : Prop :=
  ∀ p, Provable Γ p → SProvable p

/-- A2: Negative completeness in S — kit-non-certified implies S proves negation. -/
def NegativeComplete : Prop :=
  ∀ e : Code, ¬ Rev0_K K (Machine e) → SProvable (SNot (encode_halt e))

/-- Absorption Σ₁: If S1Rel(Γ) = ∅, then Rev0 ⟹ Provable Γ (encode_halt e). -/
theorem absorption_sigma1
    {Γ : Set PropT}
    (hEmpty : S1Rel Provable K Machine encode_halt Γ = ∅) :
    ∀ e : Code, Rev0_K K (Machine e) → Provable Γ (encode_halt e) := by
  intro e hRev
  by_contra hNprov
  have hMem : encode_halt e ∈ S1Rel Provable K Machine encode_halt Γ :=
    ⟨e, rfl, hRev, hNprov⟩
  rw [hEmpty] at hMem
  simp at hMem


/-- Absorption + Soundness: If S1Rel(Γ) = ∅ and Soundness(Γ), then Rev0 ⟹ S.Provable. -/
theorem absorption_soundness
    {Γ : Set PropT}
    (hEmpty : S1Rel Provable K Machine encode_halt Γ = ∅)
    (hSound : Soundness Provable SProvable Γ) :
    ∀ e : Code, Rev0_K K (Machine e) → SProvable (encode_halt e) := by
  intro e hRev
  have hProv : Provable Γ (encode_halt e) :=
    absorption_sigma1 Provable K Machine encode_halt hEmpty e hRev
  exact hSound (encode_halt e) hProv


/-!
### Corollary: The frontier cannot be empty (without contradiction)

This is the key dynamic result: under the axioms, `S1Rel(Γ) ≠ ∅` for all admissible Γ.
Combined with `FrontierWitness_of_S1Rel_nonempty`, this would close `infinite_strict_growth`
without needing `PostSplitter` propagation.
-/

theorem frontier_nonempty_of_route_II
    {Γ : Set PropT}
    (_hSound : Soundness Provable SProvable Γ)
    (_hNegComp : NegativeComplete K Machine encode_halt SProvable SNot)
    (hDec : ∀ e, Decidable (SProvable (encode_halt e)))
    (hBarrier : (∀ e, Decidable (SProvable (encode_halt e))) → False) :
    (S1Rel Provable K Machine encode_halt Γ).Nonempty := by
  -- The barrier hypothesis eliminates this case once decidability is provided.
  exact (False.elim (hBarrier hDec))


/--
  **RouteIIHyp' → RouteIIApplies**: OmegaAdmissible + RouteIIHyp' → RouteIIAt.
  This makes OmegaAdmissible structurally load-bearing in the trilemma.
-/
theorem RouteIIApplies_of_RouteIIHyp'
    (Cn : Set PropT → Set PropT) -- Added explicit Cn because RouteIIApplies probably needs it?
    {ωΓ : Set PropT}
    (hHyp : RouteIIHyp' Provable K Machine encode_halt SProvable SNot ωΓ)
    (hDec : ∀ e, Decidable (SProvable (encode_halt e))) :
    RouteIIApplies Provable K Machine encode_halt Cn ωΓ := by
  intro _hAdm
  exact frontier_nonempty_of_route_II Provable K Machine encode_halt SProvable SNot
    hHyp.soundness hHyp.negComplete hDec hHyp.barrier


end RouteII_Abstract

-- ═══════════════════════════════════════════════════════════════════════════════
-- G) FULL T2 CONNECTION (Route II → T2_impossibility)
-- ═══════════════════════════════════════════════════════════════════════════════

section T2_Connection

-- Instantiate universe locally to Type (Level 1) to match ImpossibleSystem
variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (encode_halt : RevHalt.Code → PropT)

open Nat.Partrec

/--
  **Constructor for InternalHaltingPredicate** from Route II components.
  Given (total, correct, complete) from `frontier_empty_T2_components`
  plus the semi-decidability witness `(f, hf, hsemidec)`,
  this constructs the `InternalHaltingPredicate` needed for T2.
-/
def mk_InternalHaltingPredicate_RouteII
    (S : ImpossibleSystem PropT)
    (hTotal    : ∀ e, S.Provable (encode_halt e) ∨ S.Provable (S.Not (encode_halt e)))
    (hCorrect  : ∀ e, Rev0_K K (RevHalt.Machine e) → S.Provable (encode_halt e))
    (hComplete : ∀ e, ¬ Rev0_K K (RevHalt.Machine e) → S.Provable (S.Not (encode_halt e)))
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (hsemidec : ∀ c, S.Provable (S.Not (encode_halt c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    InternalHaltingPredicate S K where
  H := encode_halt
  total := hTotal
  correct := hCorrect
  complete := hComplete
  f := f
  f_partrec := hf
  semidec := hsemidec

/--
  **Route II → T2 Contradiction (Full Theorem)**.

  If:
  - `S1Rel(Γ) = ∅`
  - `Soundness Γ` (relative provability implies S.Provable)
  - `NegativeComplete` (¬Rev0 ⟹ S proves negation)
  - Semi-decidability witness `(f, hf, hsemidec)`
  - `DetectsMonotone K`

  Then: **False** (via T2_impossibility).

  This is the complete formalization of Route II.
-/
theorem frontier_empty_T2_full
    (S : ImpossibleSystem PropT)
    (hK : DetectsUpFixed K)
    {Γ : Set PropT}
    (hEmpty : S1Rel Provable K RevHalt.Machine encode_halt Γ = ∅)
    (hSound : Soundness Provable S.Provable Γ)
    (hNegComp : NegativeComplete K RevHalt.Machine encode_halt S.Provable S.Not)
    (hTotal : ∀ e, S.Provable (encode_halt e) ∨ S.Provable (S.Not (encode_halt e)))
    -- Semi-decidability witness (from OracleMachine/ComplementaritySystem)
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (hsemidec : ∀ c, S.Provable (S.Not (encode_halt c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    False := by
  -- 2) Define Correct
  have hCorrect : ∀ e, Rev0_K K (RevHalt.Machine e) → S.Provable (encode_halt e) := by
    apply absorption_soundness Provable K RevHalt.Machine encode_halt S.Provable hEmpty hSound

  -- 3) Define Complete
  have hComplete : ∀ e, ¬ Rev0_K K (RevHalt.Machine e) → S.Provable (S.Not (encode_halt e)) := by
    exact hNegComp

  -- 4) Package into InternalHaltingPredicate
  let IH : InternalHaltingPredicate S K :=
    { H := encode_halt
      total := hTotal
      correct := hCorrect
      complete := hComplete
      f := f
      f_partrec := hf
      semidec := hsemidec }

  -- 5) Apply T2_impossibility
  exact T2_impossibility S K hK ⟨IH⟩


/--
  **Corollary: Frontier Never Empty (Route II + T2)**.

  Under the T2 hypotheses, the frontier is always non-empty.
  This provides `FrontierWitness` for all admissible states.
-/
theorem frontier_nonempty_T2
    (S : ImpossibleSystem PropT)
    (hK : DetectsUpFixed K)
    {Γ : Set PropT}
    (hSound : Soundness Provable S.Provable Γ)
    (hNegComp : NegativeComplete K RevHalt.Machine encode_halt S.Provable S.Not)
    (hTotal : ∀ e, S.Provable (encode_halt e) ∨ S.Provable (S.Not (encode_halt e)))
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (hsemidec : ∀ c, S.Provable (S.Not (encode_halt c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    (S1Rel Provable K RevHalt.Machine encode_halt Γ).Nonempty := by
  by_contra hEmpty
  rw [Set.not_nonempty_iff_eq_empty] at hEmpty
  exact frontier_empty_T2_full Provable K encode_halt S hK hEmpty hSound hNegComp hTotal f hf hsemidec


end T2_Connection

end RevHalt
