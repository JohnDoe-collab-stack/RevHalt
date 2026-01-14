import RevHalt.Theory.TheoryDynamics
import Mathlib.Data.Set.Basic
import RevHalt.Theory.Categorical

namespace RevHalt

open Set
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- TWO-SIDED DYNAMICS (Generative Complementarity)
-- ═══════════════════════════════════════════════════════════════════════════════

section TwoSidedDynamics

universe u

variable {PropT : Type u}
variable (Provable : Set PropT → PropT → Prop)
variable {Code : Type u}
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt encode_not_halt : Code → PropT)

/--
  **Two-Sided Pick**: A sentence p paired with a certificate.

  The certificate ties p to either:
  - `Rev0` (halting witness) -> p = encode_halt e
  - `KitStabilizes` (non-halting witness) -> p = encode_not_halt e

  Crucially, this structure carries the certificate *without deciding* which case holds.
  It acts as a "candidate generator" for the theory.
-/
structure TwoPick (Γ : Set PropT) (e : Code) where
  p : PropT
  cert :
    (Rev0_K K (Machine e) ∧ p = encode_halt e) ∨
    (KitStabilizes K (Machine e) ∧ p = encode_not_halt e)
  unprov : ¬ Provable Γ p

/--
  **S1Rel±(Γ)**: The two-sided dynamic frontier.

  This set contains all sentences backed by a TwoPick certificate that are NOT
  currently provable in Γ. It acts as a bidirectional source of new axioms.
-/
def S1Rel_pm (Γ : Set PropT) : Set PropT :=
  { p | ∃ e : Code,
      ∃ pk : TwoPick Provable K Machine encode_halt encode_not_halt Γ e,
        p = pk.p }

/--
  **F0±(Γ)**: The two-sided expansion step.
-/
def F0_pm (Γ : Set PropT) : Set PropT :=
  Γ ∪ S1Rel_pm Provable K Machine encode_halt encode_not_halt Γ

/--
  **Bridging Lemma**: The One-Sided frontier is a subset of the Two-Sided frontier.

  This allows us to lift any "frontier non-empty" result from the One-Sided theory
  (e.g., from Route II/T2) directly to the Two-Sided theory.
-/
theorem S1Rel_subset_S1Rel_pm
    (Γ : Set PropT) :
    S1Rel Provable K Machine encode_halt Γ ⊆
      S1Rel_pm Provable K Machine encode_halt encode_not_halt Γ := by
  intro p hp
  rcases hp with ⟨e, rfl, hKit, hNprov⟩
  -- Construct the TwoPick witness
  exact ⟨e, {
    p := encode_halt e
    cert := Or.inl ⟨hKit, rfl⟩
    unprov := hNprov
  }, rfl⟩

/--
  **S1± is Anti-Monotone**:
  As the theory grows (Γ ⊆ Δ), the set of unprovable certified sentences shrinks.
-/
theorem S1Rel_pm_anti_monotone
    (hMono : ProvRelMonotone Provable)
    {Γ Δ : Set PropT} (hSub : Γ ⊆ Δ) :
    S1Rel_pm Provable K Machine encode_halt encode_not_halt Δ ⊆
    S1Rel_pm Provable K Machine encode_halt encode_not_halt Γ := by
  intro p hp
  rcases hp with ⟨e, pk, hpEq⟩
  -- Explicitly construct the witness for Δ (target is Γ)
  -- pk is in Δ (so unprovable in Δ). We want pk in Γ (unprovable in Γ).
  exact ⟨e, {
    p := pk.p
    cert := pk.cert
    unprov := fun hProvΓ => pk.unprov (hMono Γ Δ hSub pk.p hProvΓ)
  }, hpEq⟩

/--
  **Conservation Law (Two-Sided)**:
  Under Absorbable (membership => provability), the frontier is exactly
  what is "missing" from the expansion.
-/
theorem missing_F0_pm_eq_S1Rel_pm_of_absorbable
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ) :
    MissingFrom Provable Γ
        (F0_pm Provable K Machine encode_halt encode_not_halt Γ)
      =
    S1Rel_pm Provable K Machine encode_halt encode_not_halt Γ := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpF0, hNprov⟩
    cases hpF0 with
    | inl hpΓ =>
        have hProv : Provable Γ p := hAbs p hpΓ
        exact False.elim (hNprov hProv)
    | inr hpS1 =>
        exact hpS1
  · intro hpS1
    refine And.intro ?_ ?_
    · exact Or.inr hpS1
    · -- Extract unprovability from the witness
      rcases hpS1 with ⟨e, pk, hpEq⟩
      intro hProvp
      have hProvpk : Provable Γ pk.p := by
        rw [hpEq] at hProvp
        exact hProvp
      exact pk.unprov hProvpk

/--
  **F0± is Monotone** (Constructive).

  Requires `DecidablePred` to decide if a frontier element has been absorbed.
-/
theorem F0_pm_monotone_of_provClosed
    {Γ Δ : Set PropT} (hSub : Γ ⊆ Δ)
    (hClosedΔ : ProvClosed Provable Δ)
    (hDecΔ : DecidablePred (fun p => Provable Δ p)) :
    F0_pm Provable K Machine encode_halt encode_not_halt Γ ⊆
    F0_pm Provable K Machine encode_halt encode_not_halt Δ := by
  intro p hp
  cases hp with
  | inl hpΓ =>
        exact Or.inl (hSub hpΓ)
  | inr hpS1Γ =>
      rcases hpS1Γ with ⟨e, pk, hpEq⟩
      -- Constructive split on absorption
      cases hDecΔ pk.p with
      | isTrue hProvΔ =>
          -- Absorbed in Δ
          have hMemΔ : pk.p ∈ Δ := hClosedΔ pk.p hProvΔ
          have : p ∈ Δ := by
            rw [hpEq]
            exact hMemΔ
          exact Or.inl this
      | isFalse hNprovΔ =>
          -- Remains in frontier S1Rel_pm(Δ)
          refine Or.inr ?_
          exact ⟨e, {
            p := pk.p
            cert := pk.cert
            unprov := hNprovΔ
          }, hpEq⟩

/--
  **F0± is Monotone** (Classical).

  Used for the functor instance where decidability is not guaranteed.
-/
theorem F0_pm_monotone_classical
    {Γ Δ : Set PropT} (hSub : Γ ⊆ Δ)
    (hClosedΔ : ProvClosed Provable Δ) :
    F0_pm Provable K Machine encode_halt encode_not_halt Γ ⊆
    F0_pm Provable K Machine encode_halt encode_not_halt Δ := by
  classical -- Essential for the axiom-free check to report 'classical'
  apply F0_pm_monotone_of_provClosed Provable K Machine encode_halt encode_not_halt hSub hClosedΔ (Classical.decPred _)

-- -----------------------------------------------------------------------------
-- Two-Sided Functor
-- -----------------------------------------------------------------------------

variable (Cn : Set PropT → Set PropT)

/-- **F±(S)**: The two-sided dynamic step (closed). -/
def F_pm (Γ : Set PropT) : Set PropT :=
  Cn (F0_pm Provable K Machine encode_halt encode_not_halt Γ)

/--
  **FState±**: Lifts the two-sided step to the category of Theory States.
-/
def FState_pm
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A : ThState (PropT := PropT) Provable Cn) :
    ThState (PropT := PropT) Provable Cn where
  Γ := F_pm Provable K Machine encode_halt encode_not_halt Cn A.Γ
  cn_closed := by
    dsimp [F_pm]
    rw [hIdem]
  prov_closed := by
    dsimp [F_pm]
    apply hProvCn

/--
  **FState± Map**: Functorial mapping for FState±.
-/
def FState_pm_map
    (hCnMono : CnMonotone Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    {A B : ThState (PropT := PropT) Provable Cn}
    (f : A ⟶ B) :
    FState_pm Provable K Machine encode_halt encode_not_halt Cn hIdem hProvCn A ⟶
    FState_pm Provable K Machine encode_halt encode_not_halt Cn hIdem hProvCn B := by
  have hAB : A.Γ ⊆ B.Γ := f.down
  refine ⟨?_⟩
  dsimp [FState_pm, F_pm]
  apply hCnMono
  apply F0_pm_monotone_classical Provable K Machine encode_halt encode_not_halt hAB B.prov_closed

/--
  **TheoryStepFunctor±**: The two-sided dynamic endofunctor.
-/
def TheoryStepFunctor_pm
    (hCnMono : CnMonotone Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) :
    ThState (PropT := PropT) Provable Cn ⥤ ThState (PropT := PropT) Provable Cn where
  obj := FState_pm Provable K Machine encode_halt encode_not_halt Cn hIdem hProvCn
  map := FState_pm_map Provable K Machine encode_halt encode_not_halt Cn hCnMono hIdem hProvCn
  map_id := fun _ => Subsingleton.elim _ _
  map_comp := fun _ _ => Subsingleton.elim _ _

end TwoSidedDynamics

end RevHalt
