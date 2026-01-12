import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.Up2Gain
import RevHalt.Base.Kit
import RevHalt.Base.Trace

/-!
Up2GainDynamics = instance canonique de TheoryDynamics avec séparation externe/interne.

Défs. (interne) : Provable Γ p := ∀ S, Up2ClosedInt Γ S → S p ;  Cn Γ := {p | Provable Γ p}.
Défs. (externe) : isGood p est certifié par (Machine,Kstd) : Rev0_K Kstd (Machine p) ↔ isGood p.
Déf. frontière : S1 Γ := S1Rel (Provable:=Provable) (K:=Kstd) (Machine:=Machine) (encode_halt:=id) Γ.

Lemme 1 (Frontière = gap) :
  S1 Γ = { p | isGood p ∧ ¬ Provable Γ p }.
Donc le “gap” est une notion relative à Γ, non une existence globale.

Lemme 2 (Pas = injection du gap) :
  F Cn Γ = Cn (Γ ∪ { p | isGood p ∧ ¬ Provable Γ p }).
Ainsi, le fichier formalise le mécanisme d’injection du gap, pas la non-vacuité du gap.
-/

namespace RevHalt
open Set
open CategoryTheory

namespace Up2GainDynamics

open RevHalt.Up2Gain

/-- PropT = positions Up2Gain. -/
abbrev PropT := Pos
abbrev Code  := Pos

/-- encode_halt = identity: the “sentence” *is* the code. -/
def encode_halt : Code → PropT := id

/-- External Good as a constant trace (monotone after `up` automatically). -/
def Machine : Code → Trace := fun p _n => isGood p

/-- Standard kit: Proj X := ∃n, X n. -/
def Kstd : RHKit := ⟨fun X => ∃ n, X n⟩

lemma DetectsMonotone_Kstd : DetectsMonotone Kstd := by
  intro X hmono
  -- Kstd.Proj X = (∃ n, X n) par définition
  exact Iff.rfl

/-- Key bridge: Rev0_K Kstd (Machine p) ↔ isGood p. -/
lemma rev0K_Machine_iff_isGood (p : Pos) :
    Rev0_K Kstd (Machine p) ↔ isGood p := by
  -- déplie Rev0_K / Rev_K / Kstd pour obtenir ∃ n, up (Machine p) n
  change (∃ n, up (Machine p) n) ↔ isGood p
  constructor
  · intro h
    have : (∃ n, Machine p n) := (RevHalt.exists_up_iff (Machine p)).1 h
    rcases this with ⟨n, hn⟩
    simpa [Machine] using hn
  · intro hg
    have : (∃ n, Machine p n) := ⟨0, by simpa [Machine] using hg⟩
    exact (RevHalt.exists_up_iff (Machine p)).2 this

/-
  ============================
  INTERNAL PROOF (no isGood!)
  ============================

  Up2Gain.Up2Closed uses isSuccess := isBase ∨ isGood.
  We define an INTERNAL closure where “success axioms” are exactly membership in Γ.
-/

/-- INTERNAL closedness: axioms are Γ, propagation rules are the same game rules. -/
def Up2ClosedInt (Γ : Set Pos) (S : Pos → Prop) : Prop :=
  (∀ p, p ∈ Γ → S p) ∧
  (∀ p, turnFn p = Turn.P → (∃ q, pCanMove p q ∧ S q) → S p) ∧
  (∀ p, turnFn p = Turn.O → hasMoves p → (∀ q, oCanMove p q → S q) → S p)

/-- INTERNAL provability: least Γ-closed predicate (intersection form). -/
def Provable (Γ : Set Pos) (p : Pos) : Prop :=
  ∀ S : Pos → Prop, Up2ClosedInt Γ S → S p

/-- INTERNAL deductive closure operator. -/
def Cn (Γ : Set Pos) : Set Pos := { p | Provable Γ p }

/-
  ===============
  Closure axioms
  ===============
-/

theorem CnExt : (∀ Γ, Γ ⊆ Cn Γ) := by
  intro Γ p hp S hS
  exact hS.1 p hp

theorem ProvRelMonotone : (∀ Γ Δ, Γ ⊆ Δ → ∀ p, Provable Γ p → Provable Δ p) := by
  intro Γ Δ hSub p hProvΓ S hClosedΔ
  -- S closed wrt Δ implies closed wrt Γ
  have hClosedΓ : Up2ClosedInt Γ S := by
    refine ⟨?_, hClosedΔ.2.1, hClosedΔ.2.2⟩
    intro q hqΓ
    exact hClosedΔ.1 q (hSub hqΓ)
  exact hProvΓ S hClosedΓ

theorem CnMonotone_int : ∀ {Γ Δ : Set Pos}, Γ ⊆ Δ → Cn Γ ⊆ Cn Δ := by
  intro Γ Δ hSub p hp
  -- hp : Provable Γ p
  exact ProvRelMonotone Γ Δ hSub p hp

/-- “Cut lemma” (key for idempotence / ProvClosedCn): provable from Cn Γ implies provable from Γ. -/
lemma cut : ∀ Γ p, Provable (Cn Γ) p → Provable Γ p := by
  intro Γ p hProvCn S hClosedΓ
  -- first show: Cn Γ ⊆ S (every Γ-closed set contains Cn Γ)
  have hCnSubS : ∀ q, q ∈ Cn Γ → S q := by
    intro q hq
    -- hq : Provable Γ q
    exact hq S hClosedΓ
  -- now S is also closed wrt Cn Γ
  have hClosedCn : Up2ClosedInt (Cn Γ) S := by
    refine ⟨?_, hClosedΓ.2.1, hClosedΓ.2.2⟩
    intro q hqCn
    exact hCnSubS q hqCn
  exact hProvCn S hClosedCn

theorem CnIdem : (∀ Γ, Cn (Cn Γ) = Cn Γ) := by
  intro Γ
  ext p
  constructor
  · intro hp
    -- hp : Provable (Cn Γ) p
    exact cut Γ p hp
  · intro hp
    -- monotonicity + CnExt gives Γ ⊆ Cn Γ, so provability lifts
    have hSub : Γ ⊆ Cn Γ := CnExt Γ
    exact ProvRelMonotone Γ (Cn Γ) hSub p hp

/-- ProvClosedCn required by TheoryDynamics.ThState: Provable (Cn Γ) p → p ∈ Cn Γ. -/
theorem ProvClosedCn_int : ∀ Γ, (∀ p, Provable (Cn Γ) p → p ∈ Cn Γ) := by
  intro Γ p hp
  -- membership in Cn Γ = Provable Γ p
  exact cut Γ p hp

/-
  ============================
  Now the perfect match to S1Rel
  ============================
-/

-- S1Rel from TheoryDynamics specialized to this instance:
abbrev S1 (Γ : Set Pos) : Set Pos :=
  RevHalt.S1Rel (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt) Γ

lemma S1_eq_good_notProvable (Γ : Set Pos) :
    S1 Γ = { p | isGood p ∧ ¬ Provable Γ p } := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨e, hpEq, hKit, hNprov⟩
    -- on prouve isGood e puis on réécrit via hpEq
    have hGood : isGood e := (rev0K_Machine_iff_isGood e).1 hKit
    -- encode_halt = id, donc p = e
    subst hpEq
    exact ⟨hGood, by simpa [encode_halt] using hNprov⟩
  · rintro ⟨hGood, hNprov⟩
    refine ⟨p, rfl, (rev0K_Machine_iff_isGood p).2 hGood, ?_⟩
    simpa [encode_halt] using hNprov

lemma F_eq_Cn_union_good_notProvable (Γ : Set Pos) :
    RevHalt.F (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
      Cn Γ
    =
    Cn (Γ ∪ { p | isGood p ∧ ¬ Provable Γ p }) := by
  -- F = Cn (Γ ∪ S1Rel Γ)
  -- et S1Rel Γ = S1 Γ
  simp [RevHalt.F, S1_eq_good_notProvable]

/-
  ============================
  Internal Pivots (Collatz Logic)
  ============================
-/

/--
Pivot interne (propagation via `shortcut`) :

Si `Ask (shortcut n)` est déjà provable depuis Γ, alors `Ask n` l’est aussi.
Aucun `isGood`, aucun `ProvideWin` : c’est un pur fait de la règle P :
`Ask n → Step n → Ask (shortcut n)`.
-/
lemma ask_mem_Cn_of_shortcut_mem_Cn (Γ : Set Pos) (n : ℕ)
    (h : Pos.Ask (shortcut n) ∈ Cn Γ) :
    Pos.Ask n ∈ Cn Γ := by
  -- `p ∈ Cn Γ` est exactement `Provable Γ p`
  show Provable Γ (Pos.Ask n)
  intro S hS

  -- 1) On récupère `S (Ask (shortcut n))` via la provabilité supposée.
  have hAskShort : S (Pos.Ask (shortcut n)) := h S hS

  -- 2) On en déduit `S (Step n)` par la clause P (move vers `Ask (shortcut n)`).
  have hStep : S (Pos.Step n) := by
    refine hS.2.1 (Pos.Step n) (by simp [turnFn]) ?_
    refine ⟨Pos.Ask (shortcut n), ?_⟩
    exact ⟨by simp [pCanMove], hAskShort⟩

  -- 3) Puis `S (Ask n)` par la clause P (move vers `Step n`).
  refine hS.2.1 (Pos.Ask n) (by simp [turnFn]) ?_
  refine ⟨Pos.Step n, ?_⟩
  exact ⟨by simp [pCanMove], hStep⟩

/-
  ============================
  Instantiate the Generic Functor
  ============================
-/

def hCnExt : RevHalt.CnExtensive (PropT := Pos) Cn := by
  intro Γ
  exact CnExt Γ

def hProvMono : RevHalt.ProvRelMonotone (PropT := Pos) Provable := by
  intro Γ Δ hSub p hp
  exact ProvRelMonotone Γ Δ hSub p hp

def hProvCn : RevHalt.ProvClosedCn (PropT := Pos) (Provable := Provable) Cn := by
  intro Γ p hp
  exact ProvClosedCn_int Γ p hp

def hCnMono : RevHalt.CnMonotone (PropT := Pos) Cn := by
  intro Γ Δ hSub
  exact CnMonotone_int hSub

def StepFunctor :
    RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn ⥤
    RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn :=
  RevHalt.TheoryStepFunctor
    (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
    (hIdem := CnIdem)
    (hProvCn := hProvCn)
    (hCnMono := hCnMono)

def mkState (Γ0 : Set Pos) : RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn where
  Γ := Cn Γ0
  cn_closed := CnIdem Γ0
  prov_closed := hProvCn Γ0


/-
  ============================
  Trajectory Definitions
  ============================
-/

/-- The single step of the dynamics: A_{n+1} = FState(A_n). -/
def step (A : RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn) :
           RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn :=
  RevHalt.FState (PropT := Pos) (Provable := Provable)
    (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn)
    (hIdem := CnIdem)
    (hProvCn := hProvCn)
    A

/-- Finite iteration A_n(Γ0). -/
def A (Γ0 : Set Pos) (n : ℕ) : RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn :=
  RevHalt.chainState
    (PropT := Pos) (Provable := Provable)
    (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn)
    (hIdem := CnIdem) (hProvCn := hProvCn)
    (mkState Γ0)
    n

@[simp] lemma A_zero (Γ0 : Set Pos) : A Γ0 0 = mkState Γ0 := rfl

@[simp] lemma A_succ (Γ0 : Set Pos) (n : ℕ) :
    A Γ0 (n+1) = step (A Γ0 n) := rfl

/-- The "raw" omega limit (union of all carriers). -/
def omegaCarrier (Γ0 : Set Pos) : Set Pos :=
  ⋃ n, (A Γ0 n).Γ

/-- The closed omega limit state. -/
def A_omega (Γ0 : Set Pos) : RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn :=
  mkState (omegaCarrier Γ0)

@[simp] lemma A_omega_Γ (Γ0 : Set Pos) :
    (A_omega Γ0).Γ = Cn (omegaCarrier Γ0) := rfl

lemma stage_le_omegaCarrier (Γ0 : Set Pos) (n : ℕ) :
    (A Γ0 n).Γ ⊆ omegaCarrier Γ0 := by
  intro p hp
  exact Set.mem_iUnion.2 ⟨n, hp⟩

lemma stage_le_Aomega (Γ0 : Set Pos) (n : ℕ) :
    (A Γ0 n).Γ ⊆ (A_omega Γ0).Γ := by
  intro p hp
  -- p ∈ omegaCarrier, then use extensivity of Cn
  have : p ∈ omegaCarrier Γ0 := stage_le_omegaCarrier Γ0 n hp
  exact hCnExt (omegaCarrier Γ0) this

/-
  ============================
  Monotonicity (Operative Lemmas)
  ============================
-/

lemma stage_le_succ (Γ0 : Set Pos) (n : ℕ) :
    (A Γ0 n).Γ ⊆ (A Γ0 (n+1)).Γ := by
  intro p hp
  -- rewrite A_{n+1} = step(A_n)
  rw [A_succ (Γ0 := Γ0) (n := n)]
  -- expose only what is needed: Γ(step A) = Cn (A.Γ ∪ S1Rel A.Γ)
  simp only [step, RevHalt.FState, RevHalt.F]
  -- goal: p ∈ Cn ( (A Γ0 n).Γ ∪ S1Rel ... )
  apply hCnExt
  exact Or.inl hp

lemma stage_mono (Γ0 : Set Pos) {n m : ℕ} (h : n ≤ m) :
    (A Γ0 n).Γ ⊆ (A Γ0 m).Γ := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact Subset.trans ih (stage_le_succ (Γ0 := Γ0) _)

/-
  ============================
  Strict Growth (Non-triviality Check)
  ============================
-/

/--
Strict growth: if Γ absorbs its members (internal provability of all axioms)
and there exists an externally certified good position not provable from Γ,
then one dynamic step strictly extends Γ.
-/
lemma strict_growth (Γ : Set Pos)
    (hAbs : RevHalt.Absorbable (PropT := Pos) (Provable := Provable) Γ)
    (hW : ∃ p : Pos, isGood p ∧ ¬ Provable Γ p) :
    Γ ⊂
      RevHalt.F (PropT := Pos) (Provable := Provable)
        (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
        Cn Γ := by
  refine ⟨?subset, ?not_superset⟩

  · -- Γ ⊆ F Γ
    intro q hq
    have hq' : q ∈ Γ ∪ { p : Pos | isGood p ∧ ¬ Provable Γ p } := Or.inl hq
    have : q ∈ Cn (Γ ∪ { p : Pos | isGood p ∧ ¬ Provable Γ p }) :=
      hCnExt (Γ ∪ { p : Pos | isGood p ∧ ¬ Provable Γ p }) hq'
    simpa [F_eq_Cn_union_good_notProvable] using this

  · -- ¬ (F Γ ⊆ Γ)
    intro hFsubΓ
    rcases hW with ⟨p, hpGood, hpNprov⟩

    have hpUnion : p ∈ Γ ∪ { q : Pos | isGood q ∧ ¬ Provable Γ q } :=
      Or.inr ⟨hpGood, hpNprov⟩

    have hpInCn :
        p ∈ Cn (Γ ∪ { q : Pos | isGood q ∧ ¬ Provable Γ q }) :=
      hCnExt (Γ ∪ { q : Pos | isGood q ∧ ¬ Provable Γ q }) hpUnion

    have hpInF :
        p ∈ RevHalt.F (PropT := Pos) (Provable := Provable)
              (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
              Cn Γ := by
      simpa [F_eq_Cn_union_good_notProvable] using hpInCn

    have hpInΓ : p ∈ Γ := hFsubΓ hpInF
    exact hpNprov (hAbs p hpInΓ)

/--
Corollary: Strict growth for the trajectory.
If the current stage absorbs itself and has a gap, the next stage is strictly larger.
-/
lemma strict_growth_stage (Γ0 : Set Pos) (n : ℕ)
    (hAbs : RevHalt.Absorbable (PropT := Pos) (Provable := Provable) (A Γ0 n).Γ)
    (hW : ∃ p : Pos, isGood p ∧ ¬ Provable (A Γ0 n).Γ p) :
    (A Γ0 n).Γ ⊂ (A Γ0 (n+1)).Γ := by
  have h_strict := strict_growth (A Γ0 n).Γ hAbs hW
  -- A (n+1) = step (A n), and (step s).Γ = F (s.Γ)
  -- We prove this equality via simple unfolding/rewriting
  rw [A_succ (Γ0 := Γ0) (n := n)]
  simp only [step, RevHalt.FState]
  exact h_strict

/-
  ============================
  ω-Collapse and ω-Trilemma
  (specialized to Up2GainDynamics)
  ============================
-/

open Classical

/-- The abstract orbit from `TheoryDynamics` (so we can reuse its theorems verbatim). -/
abbrev chain (Γ0 : Set Pos) : ℕ →
    RevHalt.ThState (PropT := Pos) (Provable := Provable) Cn :=
  RevHalt.chainState
    (PropT := Pos) (Provable := Provable)
    (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn)
    (hIdem := CnIdem) (hProvCn := hProvCn)
    (mkState Γ0)

/-- The raw ω-union carrier from `TheoryDynamics`. -/
abbrev ωΓ (Γ0 : Set Pos) : Set Pos :=
  RevHalt.omegaΓ
    (PropT := Pos) (Provable := Provable)
    (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn)
    (hIdem := CnIdem) (hProvCn := hProvCn)
    (mkState Γ0)

/--
RouteIIAt is literally “there exists an externally good but not internally provable position”.
This is the clean bridge between the abstract trilemma statement and your `isGood`-reading.
-/
lemma RouteIIAt_iff_exists_gap (Γ : Set Pos) :
    RevHalt.RouteIIAt
      (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
      Γ
    ↔ ∃ p : Pos, isGood p ∧ ¬ Provable Γ p := by
  -- RouteIIAt Γ = (S1Rel ... Γ).Nonempty
  unfold RevHalt.RouteIIAt
  change (S1 Γ).Nonempty ↔ _
  rw [S1_eq_good_notProvable]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩

/--
ω-collapse (specialized):
if stage 1 is absorbable, then the ω-frontier is empty.
-/
theorem S1_ωΓ_eq_empty_of_absorbable_succ (Γ0 : Set Pos)
    (hAbs1 :
      RevHalt.Absorbable (PropT := Pos) (Provable := Provable)
        ((chain Γ0 1).Γ)) :
    S1 (ωΓ Γ0) = ∅ := by
  -- This is the generic ω-collapse theorem from TheoryDynamics, instantiated.
  simpa [S1, chain, ωΓ] using
    RevHalt.S1Rel_omegaΓ_eq_empty_of_absorbable_succ
      (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn)
      (hMono := hProvMono)
      (hCnExt := hCnExt)
      (hIdem := CnIdem)
      (hProvCn := hProvCn)
      (A0 := mkState Γ0)
      hAbs1

/--
The ω-trilemma (disjunction form), specialized:
at least one of the three properties must fail:
1) absorbability at stage 1,
2) ω-admissibility of the raw ω-union,
3) Route II applicability (i.e. a gap exists at ω).
-/
theorem omega_trilemma_disjunction_up2gain (Γ0 : Set Pos) :
    ¬ RevHalt.Absorbable (PropT := Pos) (Provable := Provable) ((chain Γ0 1).Γ)
    ∨ ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable)
          (Cn := Cn) (ωΓ Γ0)
    ∨ ¬ RevHalt.RouteIIAt
          (PropT := Pos) (Provable := Provable)
          (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
          (ωΓ Γ0) := by
  simpa [chain, ωΓ] using
    RevHalt.omega_trilemma_disjunction
      (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn)
      (hMono := hProvMono)
      (hCnExt := hCnExt)
      (hIdem := CnIdem)
      (hProvCn := hProvCn)
      (A0 := mkState Γ0)

/--
Same trilemma, “not all at once” form (often the easiest to use in practice).
-/
theorem omega_trilemma_not_all_up2gain (Γ0 : Set Pos) :
    ¬ ( RevHalt.Absorbable (PropT := Pos) (Provable := Provable) ((chain Γ0 1).Γ)
      ∧ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable)
            (Cn := Cn) (ωΓ Γ0)
      ∧ RevHalt.RouteIIAt
            (PropT := Pos) (Provable := Provable)
            (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
            (ωΓ Γ0) ) := by
  simpa [chain, ωΓ] using
    RevHalt.omega_trilemma_not_all
      (PropT := Pos) (Provable := Provable)
      (K := Kstd) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn)
      (hMono := hProvMono)
      (hCnExt := hCnExt)
      (hIdem := CnIdem)
      (hProvCn := hProvCn)
      (A0 := mkState Γ0)

end Up2GainDynamics
end RevHalt

/-!
  ============================
  Drift counterexample (Option B)
  ============================

  Key idea:
  If Γ contains every `Ask n`, then `Root` is internally provable from Γ
  by the O-rule (infinitary branching at Root).

  Therefore, if at the ω-union we have all `Ask n` but still `Root ∉ ωΓ`,
  then `Cn (ωΓ) ≠ ωΓ`, hence `ωΓ` is not OmegaAdmissible.
-/

namespace RevHalt
namespace Up2GainDynamics

open Set
open RevHalt.Up2Gain

/-- If Γ contains all `Ask n`, then `Root` is internally provable from Γ. -/
lemma root_mem_Cn_of_allAsk (Γ : Set Pos)
    (hAsk : ∀ n : ℕ, Pos.Ask n ∈ Γ) :
    Pos.Root ∈ Cn Γ := by
  -- membership in Cn is Provable
  show Provable Γ Pos.Root
  intro S hS
  -- all Ask n are in S because they are Γ-axioms
  have hAskS : ∀ n : ℕ, S (Pos.Ask n) := by
    intro n
    exact hS.1 (Pos.Ask n) (hAsk n)

  -- Root has moves
  have hMoves : hasMoves Pos.Root := by
    refine ⟨Pos.Ask 0, ?_⟩
    -- canMove Root (Ask 0) reduces to oCanMove Root (Ask 0)
    simp [canMove, turnFn, oCanMove]

  -- all O-moves from Root land in S (because they are all Ask n)
  have hAll : ∀ q : Pos, oCanMove Pos.Root q → S q := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact hAskS n

  -- apply the O-closure clause at Root
  exact hS.2.2 Pos.Root (by simp [turnFn]) hMoves hAll

/-- “Pure drift” criterion: if Γ has all Ask n but not Root, then Γ is not ω-admissible. -/
theorem not_OmegaAdmissible_of_allAsk_rootNot (Γ : Set Pos)
    (hAsk : ∀ n : ℕ, Pos.Ask n ∈ Γ)
    (hRoot : Pos.Root ∉ Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) Γ := by
  intro hOA
  have hEq : Cn Γ = Γ := hOA.1
  have hRootCn : Pos.Root ∈ Cn Γ := root_mem_Cn_of_allAsk (Γ := Γ) hAsk
  have : Pos.Root ∈ Γ := by simpa [hEq] using hRootCn
  exact hRoot this

/--
Drift specialized to your ω-union `ωΓ Γ0`:

If every Ask n appears somewhere along the orbit (hence in ωΓ),
and Root never appears at any finite stage (hence not in ωΓ),
then ωΓ is not OmegaAdmissible.
-/
theorem drift_not_OmegaAdmissible_ωΓ_of_progressive_asks (Γ0 : Set Pos)
    (hAsk : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (chain Γ0 k).Γ)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) := by
  -- derive: all Ask n are in ωΓ
  have hAskω : ∀ n : ℕ, Pos.Ask n ∈ ωΓ Γ0 := by
    intro n
    rcases hAsk n with ⟨k, hk⟩
    -- ωΓ Γ0 = {p | ∃ k, p ∈ (chain Γ0 k).Γ}
    exact ⟨k, hk⟩

  -- derive: Root is not in ωΓ
  have hRootω : Pos.Root ∉ ωΓ Γ0 := by
    intro h
    rcases h with ⟨k, hk⟩
    exact hRoot k hk

  -- conclude by the pure drift criterion
  exact not_OmegaAdmissible_of_allAsk_rootNot (Γ := ωΓ Γ0) hAskω hRootω

/-
  ============================
  Arithmetic Bridge for Drift (Ask n entry mechanism)
  ============================
-/

/-- Il existe un certificat de victoire “externe” pour l’index n, présent dans la frontière S1. -/
def WinFrontierAt (Γ : Set Pos) (n : ℕ) : Prop :=
  ∃ L g m : ℕ, Pos.ProvideWin L n g m ∈ S1 Γ

/-- (A) Si un `ProvideWin L n g m` est axiome, alors `Ask n` est dans `Cn`. -/
lemma ask_mem_Cn_of_provideWin_mem (Γ : Set Pos) (L n g m : ℕ)
    (h : Pos.ProvideWin L n g m ∈ Γ) :
    Pos.Ask n ∈ Cn Γ := by
  -- membership in Cn = Provable
  show Provable Γ (Pos.Ask n)
  intro S hS
  have hWin : S (Pos.ProvideWin L n g m) := hS.1 _ h

  -- Step n est prouvé via le coup P vers ProvideWin L n g m
  have hStep : S (Pos.Step n) := by
    have hMove : (∃ q, pCanMove (Pos.Step n) q ∧ S q) := by
      refine ⟨Pos.ProvideWin L n g m, ?_, hWin⟩
      -- pCanMove (Step n) (ProvideWin L n g m)
      -- se prouve par la branche ∃ L g m, q = ProvideWin L n g m
      dsimp [pCanMove]
      exact Or.inr ⟨L, g, m, rfl⟩
    exact hS.2.1 (Pos.Step n) (by simp [turnFn]) hMove

  -- Ask n est prouvé via le coup P vers Step n
  have hMoveAsk : (∃ q, pCanMove (Pos.Ask n) q ∧ S q) := by
    refine ⟨Pos.Step n, ?_, hStep⟩
    -- pCanMove (Ask n) (Step n)
    simp [pCanMove]
  exact hS.2.1 (Pos.Ask n) (by simp [turnFn]) hMoveAsk

/-- (B) Si `WinFrontierAt (Γ_k) n` est vrai, alors `Ask n` est vrai au stade k+1/step. -/
lemma ask_mem_stage_succ_of_winFrontier (Γ0 : Set Pos) (k n : ℕ)
    (hW : WinFrontierAt ((A Γ0 k).Γ) n) :
    Pos.Ask n ∈ (A Γ0 (k+1)).Γ := by
  rcases hW with ⟨L, g, m, hS1⟩
  -- réécrire A_{k+1}
  rw [A_succ (Γ0 := Γ0) (n := k)]
  -- exposer la définition : Γ(step A_k) = Cn (Γ_k ∪ S1 Γ_k)
  simp only [step, RevHalt.FState, RevHalt.F]

  -- il suffit de prouver Ask n ∈ Cn (Γ_k ∪ S1 Γ_k)
  -- en utilisant que ProvideWin L n g m est dans S1 Γ_k donc dans l’union
  have hUnion : Pos.ProvideWin L n g m ∈ ((A Γ0 k).Γ ∪ S1 ((A Γ0 k).Γ)) :=
    Or.inr hS1

  exact ask_mem_Cn_of_provideWin_mem
    (Γ := (A Γ0 k).Γ ∪ S1 ((A Γ0 k).Γ)) (L := L) (n := n) (g := g) (m := m) hUnion

/-- (C) Propriété de "couverture progressive" par des gains. -/
def ProgressiveWins (Γ0 : Set Pos) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, WinFrontierAt ((A Γ0 k).Γ) n

/-- Hypothèse séquentielle : à chaque étape k, on obtient un win pour `schedule k`. -/
def StepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, WinFrontierAt ((A Γ0 k).Γ) (schedule k)

/-- Fairness (couverture) : chaque n apparaît à un certain rang dans `schedule`. -/
def FairSchedule (schedule : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, schedule k = n

/-- StepwiseWins + fairness ⇒ ProgressiveWins. -/
lemma progressiveWins_of_stepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule) :
    ProgressiveWins Γ0 := by
  intro n
  rcases hFair n with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  -- hStep k : WinFrontierAt ((A Γ0 k).Γ) (schedule k)
  simpa [hk] using hStep k

/-- ProgressiveWins implies eventually finding Ask n. -/
lemma progressive_asks_of_progressiveWins (Γ0 : Set Pos)
    (hProg : ProgressiveWins Γ0) :
    ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ := by
  intro n
  rcases hProg n with ⟨k, hW⟩
  refine ⟨k+1, ?_⟩
  exact ask_mem_stage_succ_of_winFrontier Γ0 k n hW

/-- Version robuste de `progressive_asks` : dérivée d’un win par étape + fairness. -/
lemma progressive_asks_of_stepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule) :
    ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ := by
  -- recycle ton lemme existant
  exact progressive_asks_of_progressiveWins Γ0
    (progressiveWins_of_stepwiseWins (Γ0 := Γ0) (schedule := schedule) hStep hFair)

/-- Conséquence finale : Option B (Drift) sans axiome global, via stepwise + fairness. -/
theorem optionB_drift_counterexample_stepwise (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) := by
  -- 1) tous les Ask n entrent (à des temps éventuellement différents)
  have hAskA : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ :=
    progressive_asks_of_stepwiseWins (Γ0 := Γ0) (schedule := schedule) hStep hFair

  -- 2) réexprimer en termes de `chain` pour utiliser le lemme drift déjà prouvé
  have hAsk : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (chain Γ0 k).Γ := by
    intro n
    rcases hAskA n with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [chain, A] using hk

  -- 3) appliquer le drift générique
  exact drift_not_OmegaAdmissible_ωΓ_of_progressive_asks Γ0 hAsk hRoot

-- ==============================================================================================
-- CANONICAL POLICY (Standard Verification Strategy)
-- ==============================================================================================

/-!
  ## Canonical Policy
  We define a concrete, constructive schedule to demonstrate that `FairSchedule` is inhabited
  and easily realizable.

  The "Standard Schedule" simply targets integer `k` at step `k`.
  Use case: The verifier systematically checks n=0, n=1, n=2...
-/

/-- Standard Schedule: at step k, we target n = k. -/
def StandardSchedule : ℕ → ℕ := id

/-- The Standard Schedule is fair (it covers every integer). -/
lemma standardSchedule_fair : FairSchedule StandardSchedule := by
  intro n
  use n
  rfl

/--
  **Canonical Drift Theorem**:
  If the system provides a win for `n` at step `n` (Diagonal Wins),
  then it drifts into Option B.

  This removes the existential quantifier on `schedule` in favor of a concrete instance.
-/
theorem canonical_drift_counterexample
    (Γ0 : Set Pos)
    (hDiagWins : StepwiseWins Γ0 StandardSchedule)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) :=
  optionB_drift_counterexample_stepwise Γ0 StandardSchedule hDiagWins standardSchedule_fair hRoot


end Up2GainDynamics
end RevHalt
