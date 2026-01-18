import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Thin


import RevHalt.Theory.Complementarity
import RevHalt.Theory.Stabilization
import RevHalt.Theory.Categorical
import RevHalt.Theory.Impossibility

/-!
# RevHalt.Theory.TheoryDynamics

Formalizes the dynamic theory functor:

  F(S) := Cn(S ∪ S1(S))

where:
- S = current theory state (post-splitter / corpus)
- S1(S) = frontier relative to S (kit-detection + non-provable in S)
- The iteration S_{n+1} = F(S_n) encodes the interdependent dynamics

## Key Insight

The frontier S1(Γ) depends on `¬Provable Γ`, so as Γ grows, S1(Γ) shrinks.
This is the "conservation law": the gap persists because extending the theory
regenerates the frontier at each step.

## Structure

1. Thin category of theories (ThObj, ThHom)
2. Relative provability (Provable : Set PropT → PropT → Prop)
3. Dynamic frontier S1Rel(Γ)
4. Step function F0, F
5. Iteration chain and ω-limit
6. Conservation law: MissingFrom = S1Rel
-/

namespace RevHalt

open Set
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) THIN CATEGORY OF THEORIES (CORPUS)
-- ═══════════════════════════════════════════════════════════════════════════════

universe u

variable {PropT : Type u}

/-- A theory object is a corpus Γ : Set PropT. -/
abbrev ThObj (PropT : Type u) := Set PropT

/-- Morphisms between theory objects are inclusions. -/
def ThHom (Γ Δ : ThObj PropT) : Prop := Γ ⊆ Δ

theorem ThHom.refl (Γ : ThObj PropT) : ThHom Γ Γ := Subset.refl Γ

theorem ThHom.trans {Γ Δ Ξ : ThObj PropT} (h1 : ThHom Γ Δ) (h2 : ThHom Δ Ξ) :
    ThHom Γ Ξ := Subset.trans h1 h2

/-- Category instance: thin category where Hom Γ Δ is a lifted Prop (inclusion). -/
instance : Category (ThObj PropT) where
  Hom Γ Δ := PLift (ThHom (PropT := PropT) Γ Δ)
  id Γ := ⟨ThHom.refl (PropT := PropT) Γ⟩
  comp f g := ⟨ThHom.trans (PropT := PropT) f.down g.down⟩
  id_comp := by
    intro Γ Δ f; cases f; rfl
  comp_id := by
    intro Γ Δ f; cases f; rfl
  assoc := by
    intro Γ Δ Ξ Ω f g h; cases f; cases g; cases h; rfl

instance (Γ Δ : ThObj PropT) : Subsingleton (Γ ⟶ Δ) := by
  refine ⟨?_⟩
  intro f g
  cases f; cases g
  rfl

/-- Convert a Prop-level inclusion into a categorical morphism. -/
def homOfThHom {Γ Δ : ThObj PropT} (h : ThHom (PropT := PropT) Γ Δ) : Γ ⟶ Δ :=
  ⟨h⟩

/-- Extract the underlying inclusion from a categorical morphism. -/
def thHomOfHom {Γ Δ : ThObj PropT} (f : Γ ⟶ Δ) : ThHom (PropT := PropT) Γ Δ :=
  f.down

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) RELATIVE PROVABILITY
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Provable : Set PropT → PropT → Prop)

/-- Provability is monotone: extending the corpus preserves provability. -/
def ProvRelMonotone : Prop :=
  ∀ Γ Δ : Set PropT, Γ ⊆ Δ → ∀ p : PropT, Provable Γ p → Provable Δ p

/--
  **ProvClosed**: A corpus is closed under its own provability.
  This is the key hypothesis for F0_monotone: provable ⇒ membership.
-/
def ProvClosed (Γ : Set PropT) : Prop :=
  ∀ p : PropT, Provable Γ p → p ∈ Γ

/--
  **PostSplitter**: A corpus where membership ⇔ provability.
  This is the strong form: S = S2(S).
-/
def PostSplitter (Γ : Set PropT) : Prop :=
  ∀ p : PropT, p ∈ Γ ↔ Provable Γ p

/-- Deductive closure operator axioms. -/
def CnExtensive (Cn : Set PropT → Set PropT) : Prop := ∀ Γ, Γ ⊆ Cn Γ
def CnMonotone  (Cn : Set PropT → Set PropT) : Prop := ∀ {Γ Δ}, Γ ⊆ Δ → Cn Γ ⊆ Cn Δ
def CnIdem      (Cn : Set PropT → Set PropT) : Prop := ∀ Γ, Cn (Cn Γ) = Cn Γ

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) DYNAMIC FRONTIER S1(Γ) — THE KEY DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

variable {Code : Type u}
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

/--
  **Dynamic Frontier S1(Γ)**:
  The set of kit-certified halting sentences that are NOT provable in Γ.

  This is the core of the interdependent dynamics:
  - S1 depends on Γ via `¬ Provable Γ (encode_halt e)`
  - As Γ grows, S1(Γ) shrinks (anti-monotone)
-/
def S1Rel (Γ : Set PropT) : Set PropT :=
  { p | ∃ e : Code,
      p = encode_halt e ∧
      Rev0_K K (Machine e) ∧
      ¬ Provable Γ (encode_halt e) }

/-- Membership lemma for S1Rel. -/
lemma mem_S1Rel_of_witness
    (Γ : Set PropT) (e : Code)
    (hKit : Rev0_K K (Machine e))
    (hNprov : ¬ Provable Γ (encode_halt e)) :
    encode_halt e ∈ S1Rel Provable K Machine encode_halt Γ := by
  exact ⟨e, rfl, hKit, hNprov⟩

/--
  **S1 is Anti-Monotone**:
  If Provable is monotone, then S1 is anti-monotone:
  Γ ⊆ Δ → S1(Δ) ⊆ S1(Γ)

  More provable ⟹ smaller frontier.
-/
theorem S1Rel_anti_monotone
    (hMono : ProvRelMonotone Provable)
    {Γ Δ : Set PropT} (hSub : Γ ⊆ Δ) :
    S1Rel Provable K Machine encode_halt Δ ⊆
    S1Rel Provable K Machine encode_halt Γ := by
  intro p hp
  obtain ⟨e, hpEq, hKit, hNprovΔ⟩ := hp
  refine ⟨e, hpEq, hKit, ?_⟩
  intro hProvΓ
  have hProvΔ : Provable Δ (encode_halt e) := hMono Γ Δ hSub (encode_halt e) hProvΓ
  exact hNprovΔ hProvΔ

/-- Post-splitter S2(Γ): what is provable in Γ. -/
def S2Rel (Γ : Set PropT) : Set PropT := { p | Provable Γ p }

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) DYNAMIC STEP F — THE ENDO-FUNCTOR
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Minimal Step F0**: Γ ↦ Γ ∪ S1(Γ)

  This is the simplest form of the dynamic step.
-/
def F0 (Γ : Set PropT) : Set PropT :=
  Γ ∪ S1Rel Provable K Machine encode_halt Γ

/--
  **Full Step F**: Γ ↦ Cn(Γ ∪ S1(Γ))

  Includes deductive closure.
-/
def F (Cn : Set PropT → Set PropT) (Γ : Set PropT) : Set PropT :=
  Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ)

@[simp] lemma F0_apply (Γ : Set PropT) :
  F0 Provable K Machine encode_halt Γ =
    Γ ∪ S1Rel Provable K Machine encode_halt Γ := rfl

@[simp] lemma F_apply (Cn : Set PropT → Set PropT) (Γ : Set PropT) :
  F Provable K Machine encode_halt Cn Γ =
    Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := rfl

/-- F0 is extensive: Γ ⊆ F0(Γ). -/
theorem F0_extensive (Γ : Set PropT) :
    Γ ⊆ F0 Provable K Machine encode_halt Γ := by
  intro p hp
  exact Or.inl hp

/--
  **F0 is Monotone under ProvClosed hypothesis** (Constructive).

  The key insight: if p ∈ S1(Γ) becomes provable in Δ, then by ProvClosed
  it must be in Δ, so p ∈ F0(Δ) via the left branch.

  Requires `DecidablePred` for constructivity.
-/
theorem F0_monotone_of_provClosed
    {Γ Δ : Set PropT} (hSub : Γ ⊆ Δ)
    (hClosedΔ : ProvClosed Provable Δ)
    (hDecΔ : DecidablePred (fun p => Provable Δ p)) :
    F0 Provable K Machine encode_halt Γ ⊆
    F0 Provable K Machine encode_halt Δ := by
  intro p hp
  cases hp with
  | inl hpΓ =>
      -- p ∈ Γ, so p ∈ Δ by inclusion
      exact Or.inl (hSub hpΓ)
  | inr hpS1Γ =>
      -- p ∈ S1(Γ): p = encode_halt e, kit ok, ¬Provable Γ (encode_halt e)
      obtain ⟨e, hpEq, hKit, hNprovΓ⟩ := hpS1Γ
      -- Constructive split
      cases hDecΔ (encode_halt e) with
      | isTrue hProvΔ =>
          have hMemΔ : encode_halt e ∈ Δ := hClosedΔ (encode_halt e) hProvΔ
          rw [hpEq]
          exact Or.inl hMemΔ
      | isFalse hProvΔ =>
          right
          exact ⟨e, hpEq, hKit, hProvΔ⟩

/-- F is monotone (assuming Cn is monotone). -/
theorem F_monotone
    (Cn : Set PropT → Set PropT)
    (hCnMono : CnMonotone Cn)
    {Γ Δ : Set PropT}
    (hF0Mono : F0 Provable K Machine encode_halt Γ ⊆ F0 Provable K Machine encode_halt Δ) :
    F Provable K Machine encode_halt Cn Γ ⊆
    F Provable K Machine encode_halt Cn Δ := by
  unfold F
  exact hCnMono hF0Mono

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) ITERATION CHAIN AND ω-LIMIT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Iteration of F0 starting from Γ0. -/
def chain0 (Γ0 : Set PropT) : ℕ → Set PropT
  | 0     => Γ0
  | n + 1 => F0 Provable K Machine encode_halt (chain0 Γ0 n)

/-- Iteration of F starting from Γ0. -/
def chain (Cn : Set PropT → Set PropT) (Γ0 : Set PropT) : ℕ → Set PropT
  | 0     => Γ0
  | n + 1 => F Provable K Machine encode_halt Cn (chain Cn Γ0 n)

/-- The chain is monotonically increasing (each step extends). -/
theorem chain0_mono_step (Γ0 : Set PropT) :
    ∀ n, chain0 Provable K Machine encode_halt Γ0 n ⊆
         chain0 Provable K Machine encode_halt Γ0 (n + 1) := by
  intro n
  -- chain0 Γ0 (n+1) = F0 (chain0 Γ0 n) = (chain0 Γ0 n) ∪ S1(chain0 Γ0 n)
  -- So chain0 Γ0 n ⊆ chain0 Γ0 n ∪ ... is trivial
  exact F0_extensive Provable K Machine encode_halt (chain0 Provable K Machine encode_halt Γ0 n)

/-- Transitivity: n ≤ m → chain0 Γ0 n ⊆ chain0 Γ0 m. -/
theorem chain0_mono (Γ0 : Set PropT) :
    ∀ n m, n ≤ m → chain0 Provable K Machine encode_halt Γ0 n ⊆
                   chain0 Provable K Machine encode_halt Γ0 m := by
  intro n m hnm
  induction hnm with
  | refl => exact Subset.refl _
  | step _ ih =>
      exact Subset.trans ih (chain0_mono_step Provable K Machine encode_halt Γ0 _)

/-- The ω-limit: union of all stages. -/
def omega0 (Γ0 : Set PropT) : Set PropT :=
  { p | ∃ n, p ∈ chain0 Provable K Machine encode_halt Γ0 n }

/-- Each stage embeds into the ω-limit. -/
theorem chain0_le_omega0 (Γ0 : Set PropT) (n : ℕ) :
    chain0 Provable K Machine encode_halt Γ0 n ⊆
    omega0 Provable K Machine encode_halt Γ0 := by
  intro p hp
  exact ⟨n, hp⟩

/-- Universal property of ω-limit. -/
theorem omega0_universal (Γ0 : Set PropT) (T : Set PropT)
    (h : ∀ n, chain0 Provable K Machine encode_halt Γ0 n ⊆ T) :
    omega0 Provable K Machine encode_halt Γ0 ⊆ T := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  exact h n hn

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5.1) OMEGA-CONTINUITY AND FIXPOINTS (Structural Core)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ω-continuity (Set version): F commutes with directed unions. -/
def OmegaContinuousSet (F : Set PropT → Set PropT) : Prop :=
  ∀ (U : ℕ → Set PropT),
    (∀ n, U n ⊆ U (n+1)) →
      F {p | ∃ n, p ∈ U n} = {p | ∃ n, p ∈ F (U n)}

/-- Chain iterated by step F. -/
def iter (F : Set PropT → Set PropT) (Γ0 : Set PropT) : ℕ → Set PropT
  | 0     => Γ0
  | n + 1 => F (iter F Γ0 n)

/-- Union (ω-limit) of a chain. -/
def omegaUnion (U : ℕ → Set PropT) : Set PropT :=
  {p | ∃ n, p ∈ U n}

/-- Technical Lemma: Shifted union equals union (for increasing chains). -/
lemma union_shift_eq_union
    (U : ℕ → Set PropT)
    (hmono : ∀ n, U n ⊆ U (n+1)) :
    {p | ∃ n, p ∈ U (n+1)} = {p | ∃ n, p ∈ U n} := by
  ext p
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      -- p ∈ U 0 ⊆ U 1
      exact ⟨0, hmono 0 hn⟩
    | succ n' =>
      exact ⟨n', hn⟩

/-- Technical Lemma: The image of the chain under F is exactly the shifted chain. -/
lemma union_iter_succ (F : Set PropT → Set PropT) (Γ0 : Set PropT) :
    {p | ∃ n, p ∈ F (iter F Γ0 n)} = {p | ∃ n, p ∈ iter F Γ0 (n+1)} := by
  ext p
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, by simpa [iter] using hn⟩
  · exact ⟨n, by simpa [iter] using hn⟩

/--
  **Structural Fixpoint Lemma**:
  If F is ω-continuous, then the limit of any F-chain is a fixpoint of F.
-/
theorem omega_fixpoint_of_OmegaContinuousSet
    (F : Set PropT → Set PropT)
    (hω : OmegaContinuousSet F)
    (Γ0 : Set PropT)
    (hmono : ∀ n, iter F Γ0 n ⊆ iter F Γ0 (n+1)) :
    F (omegaUnion (iter F Γ0)) =
      omegaUnion (iter F Γ0) := by
  dsimp [omegaUnion]
  -- F(⋃ Γn) = ⋃ F(Γn) by continuity
  rw [hω (iter F Γ0) hmono]
  -- ⋃ F(Γn) = ⋃ Γ(n+1) by iter structure
  rw [union_iter_succ F Γ0]
  -- ⋃ Γ(n+1) = ⋃ Γn by shift lemma (using mono)
  exact union_shift_eq_union (iter F Γ0) hmono

/--
  **Structural Escape Theorem (Abstract)**:
  If the limit is NOT a fixpoint, then F CANNOT be ω-continuous.
  This is the categorical formulation of the "Incarnation means rupture" thesis.
-/
theorem not_omegaContinuous_of_no_fixpoint
    (F : Set PropT → Set PropT)
    (Γ0 : Set PropT)
    (hmono : ∀ n, iter F Γ0 n ⊆ iter F Γ0 (n+1))
    (hNoFix : F (omegaUnion (iter F Γ0)) ≠ omegaUnion (iter F Γ0)) :
    ¬ OmegaContinuousSet F := by
  intro hω
  have hFix := omega_fixpoint_of_OmegaContinuousSet F hω Γ0 hmono
  exact hNoFix hFix

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) CONSERVATION LAW — "MISSING = S1"
-- ═══════════════════════════════════════════════════════════════════════════════

/-- What the step adds but is not provable in Γ. -/
def MissingFrom (Γ Δ : Set PropT) : Set PropT :=
  { p | p ∈ Δ ∧ ¬ Provable Γ p }

/--
  **Absorbable**: The state has absorbed all its members into its provability relation.
  Formally: `p ∈ Γ → Provable Γ p`.

  This is the *closure of membership* property.
  (It is the dual of `ProvClosed`, which is `Provable Γ p → p ∈ Γ`).
-/
def Absorbable (Γ : Set PropT) : Prop := ∀ p, p ∈ Γ → Provable Γ p

/--
  **Conservation Law (Subtraction Property)**:
  If Γ is absorbable (post-splitter), then:
    MissingFrom Γ (F0 Γ) = S1(Γ)

  This is the dynamic version of `missing_equals_S1` from Complementarity.lean.
-/
theorem missing_F0_eq_S1_of_absorbable
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ) :
    MissingFrom Provable Γ (F0 Provable K Machine encode_halt Γ) =
    S1Rel Provable K Machine encode_halt Γ := by
  ext p
  constructor
  · -- MissingFrom → S1
    intro hp
    obtain ⟨hpF0, hNprov⟩ := hp
    cases hpF0 with
    | inl hpΓ =>
        -- p ∈ Γ but ¬Provable Γ p, contradicts Absorbable
        have hProv : Provable Γ p := hAbs p hpΓ
        exact False.elim (hNprov hProv)
    | inr hpS1 =>
        exact hpS1
  · -- S1 → MissingFrom
    intro hpS1
    constructor
    · exact Or.inr hpS1
    · obtain ⟨e, hpEq, _hKit, hNprov⟩ := hpS1
      rw [hpEq]
      exact hNprov


/--
  **Strict Extension (with Absorbable hypothesis)**:
  Under absorbability, a witness gives strict extension.
-/
theorem strict_step_of_witness_absorbable
    (Γ : Set PropT)
    (hAbs : Absorbable Provable Γ)
    (e : Code)
    (hKit : Rev0_K K (Machine e))
    (hNprov : ¬ Provable Γ (encode_halt e)) :
    Γ ⊂ F0 Provable K Machine encode_halt Γ := by
  constructor
  · exact F0_extensive Provable K Machine encode_halt Γ
  · intro hContra
    have hMem : encode_halt e ∈ S1Rel Provable K Machine encode_halt Γ :=
      ⟨e, rfl, hKit, hNprov⟩
    have hMemF0 : encode_halt e ∈ F0 Provable K Machine encode_halt Γ :=
      Or.inr hMem
    have hMemΓ : encode_halt e ∈ Γ := hContra hMemF0
    have hProv : Provable Γ (encode_halt e) := hAbs (encode_halt e) hMemΓ
    exact hNprov hProv

/--
  **Frontier Non-Annihilation**:
  If at every stage there exists a witness, then the frontier is non-empty at all stages.
-/
theorem frontier_nonempty_all_stages
    (Γ0 : Set PropT)
    (H : ∀ Γ : Set PropT, (S1Rel Provable K Machine encode_halt Γ).Nonempty) :
    ∀ n, (S1Rel Provable K Machine encode_halt
            (chain0 Provable K Machine encode_halt Γ0 n)).Nonempty := by
  intro n
  exact H _

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) BRIDGE TO TRACE KERNEL
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **S1Rel witness implies trace not in kernel (witness-based)**.

  If p ∈ S1Rel Γ, we get a witness e with Kit-certified halting.
  Thus Machine e cannot be in upKernel (stabilization).

  This is the correct formulation without requiring encode_halt injectivity.
-/
theorem S1Rel_witness_not_in_kernel
    (hK : DetectsUpFixed K)
    {Γ : Set PropT} {p : PropT}
    (hp : p ∈ S1Rel Provable K Machine encode_halt Γ) :
    ∃ e : Code,
      p = encode_halt e ∧
      Rev0_K K (Machine e) ∧
      Machine e ∉ Categorical.upKernel := by
  obtain ⟨e, hpEq, hKit, _hNprov⟩ := hp
  refine ⟨e, hpEq, hKit, ?_⟩
  -- Machine e ∉ upKernel because Kit certifies halting
  intro hContra
  have hHalts : Halts (Machine e) := (T1_traces K hK (Machine e)).mp hKit
  have hStab : ∀ n, ¬ (Machine e) n :=
    (RevHalt.Categorical.mem_upKernel_iff (T := Machine e)).mp hContra
  obtain ⟨n, hn⟩ := hHalts
  exact hStab n hn

/--
  **Connection**: Kit-certified halting means NOT in kernel.
-/
theorem kit_certified_not_in_kernel
    (hK : DetectsUpFixed K)
    (e : Code)
    (hKit : Rev0_K K (Machine e)) :
    Machine e ∉ Categorical.upKernel := by
  intro hContra
  have hHalts : Halts (Machine e) := (T1_traces K hK (Machine e)).mp hKit
  have hStab : ∀ n, ¬ (Machine e) n :=
    (RevHalt.Categorical.mem_upKernel_iff (T := Machine e)).mp hContra
  obtain ⟨n, hn⟩ := hHalts
  exact hStab n hn

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) THE TRUE DYNAMIC FUNCTOR (Complete Formalization)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Dynamic Functor on Admissible Theory States

To make F a true endo-functor, the target must remain in the category.
This requires theory states that are:
1. **Cn-closed**: Cn Γ = Γ (fixed point of deductive closure)
2. **ProvClosed**: Provable Γ p → p ∈ Γ (membership captures provability)

The key axiom `ProvClosedCn` states that Cn produces ProvClosed sets.
This makes FState an endo-functor without external hypotheses.
-/

section Functor

variable (Cn : Set PropT → Set PropT)

/-- Cn produces ProvClosed sets (key structural axiom). -/
def ProvClosedCn : Prop := ∀ Γ, ProvClosed Provable (Cn Γ)

/--
  **ThState**: An admissible theory state.
  - Cn-closed: fixed point of deductive closure
  - ProvClosed: provability implies membership
-/
structure ThState where
  Γ : Set PropT
  cn_closed : Cn Γ = Γ
  prov_closed : ProvClosed Provable Γ

/-- Morphisms between ThState objects are inclusions of carriers. -/
def ThStateHom (A B : ThState Provable Cn) : Prop := A.Γ ⊆ B.Γ

theorem ThStateHom.refl (A : ThState Provable Cn) : ThStateHom Provable Cn A A :=
  Subset.refl A.Γ

theorem ThStateHom.trans {A B C : ThState Provable Cn}
    (h1 : ThStateHom Provable Cn A B) (h2 : ThStateHom Provable Cn B C) :
    ThStateHom Provable Cn A C :=
  Subset.trans h1 h2

-- Category instance for ThState
instance : Category (ThState (PropT := PropT) Provable Cn) where
  Hom A B := PLift (ThStateHom Provable Cn A B)
  id A := ⟨ThStateHom.refl Provable Cn A⟩
  comp f g := ⟨ThStateHom.trans Provable Cn f.down g.down⟩
  id_comp := by
    intro A B f; cases f; rfl
  comp_id := by
    intro A B f; cases f; rfl
  assoc := by
    intro A B C D f g h; cases f; cases g; cases h; rfl

instance (A B : ThState (PropT := PropT) Provable Cn) : Subsingleton (A ⟶ B) := by
  refine ⟨?_⟩
  intro f g
  cases f; cases g
  rfl

/--
  **FState**: The dynamic step applied to an admissible theory state.
  - Result is Cn-closed via CnIdem
  - Result is ProvClosed via ProvClosedCn
-/
def FState
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A : ThState (PropT := PropT) Provable Cn) : ThState (PropT := PropT) Provable Cn where
  Γ := F Provable K Machine encode_halt Cn A.Γ
  cn_closed := by
    unfold F
    exact hIdem (A.Γ ∪ S1Rel Provable K Machine encode_halt A.Γ)
  prov_closed := by
    unfold F
    exact hProvCn (A.Γ ∪ S1Rel Provable K Machine encode_halt A.Γ)

/--
  **FState preserves morphisms (functoriality)**:
  If A.Γ ⊆ B.Γ, then FState(A).Γ ⊆ FState(B).Γ.
  Uses B.prov_closed from the structure (no external argument).
-/
theorem FState_map
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hCnMono : CnMonotone Cn)
    {A B : ThState (PropT := PropT) Provable Cn}
    (hAB : ThStateHom Provable Cn A B) :
    ThStateHom Provable Cn
      (FState Provable K Machine encode_halt Cn hIdem hProvCn A)
      (FState Provable K Machine encode_halt Cn hIdem hProvCn B) := by
  unfold FState ThStateHom
  apply F_monotone Provable K Machine encode_halt Cn hCnMono
  -- Use classical decidability for the functor map existence
  classical
  exact F0_monotone_of_provClosed Provable K Machine encode_halt hAB B.prov_closed (Classical.decPred _)

/--
  **TheoryStepFunctor**: The endo-functor `F : ThState ⥤ ThState`.
  In a thin category, `map_id` and `map_comp` are trivial.
-/
def TheoryStepFunctor
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hCnMono : CnMonotone Cn) :
    ThState (PropT := PropT) Provable Cn ⥤
    ThState (PropT := PropT) Provable Cn where
  obj := FState Provable K Machine encode_halt Cn hIdem hProvCn
  map f := ⟨FState_map Provable K Machine encode_halt Cn hIdem hProvCn hCnMono f.down⟩
  map_id := fun _ => Subsingleton.elim _ _
  map_comp := fun _ _ => Subsingleton.elim _ _

/--
  **The chain on ThState**: iteration of the functor.
-/
def chainState
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) : ℕ → ThState (PropT := PropT) Provable Cn
  | 0     => A0
  | n + 1 => FState Provable K Machine encode_halt Cn hIdem hProvCn (chainState hIdem hProvCn A0 n)

@[simp] lemma mem_chainState_succ
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (n : ℕ) (p : PropT) :
    p ∈ (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ ↔
    p ∈ Cn ((chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ∪
            S1Rel Provable K Machine encode_halt (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ) := by
  rfl

/--
  **Chain step morphism**: Each stage embeds into the next.
  Uses CnExtensive to show Γ_n ⊆ Γ_{n+1}.
-/
theorem chainState_step_hom
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hCnExt : CnExtensive Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (n : ℕ) :
    ThStateHom Provable Cn
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)) := by
  intro p hp
  -- Force the form of the goal: step n+1 = FState (step n)
  change p ∈
    (FState Provable K Machine encode_halt Cn hIdem hProvCn
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)).Γ
  -- Unfold only FState then F (not chainState) for stability
  simp only [FState, F]
  -- Goal: p ∈ Cn ((Γn) ∪ S1Rel(Γn))
  apply hCnExt
  exact Or.inl hp

-- Simp lemmas for stability
@[simp] lemma FState_Γ
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A : ThState (PropT := PropT) Provable Cn) :
    (FState Provable K Machine encode_halt Cn hIdem hProvCn A).Γ
      = F Provable K Machine encode_halt Cn A.Γ := rfl

@[simp] lemma chainState_succ
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) (n : ℕ) :
    chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n+1)
      = FState Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n) := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- A) WITNESS => S1Rel NONEMPTY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A concrete RevHalt-style witness that the frontier is nonempty at Γ. -/
def FrontierWitness (Γ : Set PropT) : Prop :=
  ∃ e : Code, Rev0_K K (Machine e) ∧ ¬ Provable Γ (encode_halt e)

/-- A witness produces a nonempty dynamic frontier. -/
theorem S1Rel_nonempty_of_witness
    {Γ : Set PropT}
    (hW : FrontierWitness Provable K Machine encode_halt Γ) :
    (S1Rel Provable K Machine encode_halt Γ).Nonempty := by
  rcases hW with ⟨e, hKit, hNprov⟩
  refine ⟨encode_halt e, ?_⟩
  exact mem_S1Rel_of_witness Provable K Machine encode_halt Γ e hKit hNprov

-- ═══════════════════════════════════════════════════════════════════════════════
-- B) NO FIXED POINT + STRICT GROWTH (core dynamics)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- If Γ is absorbable and has a frontier witness, Γ cannot be a fixed point of F. -/
theorem not_fixpoint_F_of_absorbable
    (hCnExt : CnExtensive Cn)
    {Γ : Set PropT}
    (hAbs : Absorbable Provable Γ)
    (hW : FrontierWitness Provable K Machine encode_halt Γ)
    (hFix : F Provable K Machine encode_halt Cn Γ = Γ) :
    False := by
  have hS1Sub : S1Rel Provable K Machine encode_halt Γ ⊆ Γ := by
    intro p hpS1
    have hUnion : p ∈ (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := Or.inr hpS1
    have hCn : p ∈ Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) :=
      (hCnExt (Γ ∪ S1Rel Provable K Machine encode_halt Γ)) hUnion
    have hF : p ∈ F Provable K Machine encode_halt Cn Γ := by
      rw [F_apply]
      exact hCn
    rw [hFix] at hF
    exact hF
  rcases hW with ⟨e, hKit, hNprov⟩
  have hMemS1 : encode_halt e ∈ S1Rel Provable K Machine encode_halt Γ :=
    mem_S1Rel_of_witness Provable K Machine encode_halt Γ e hKit hNprov
  have hMemΓ : encode_halt e ∈ Γ := hS1Sub hMemS1
  have hProv : Provable Γ (encode_halt e) := hAbs _ hMemΓ
  exact hNprov hProv

/-- Under absorbability + witness, the dynamic step strictly extends Γ. -/
theorem strict_F_of_absorbable
    (hCnExt : CnExtensive Cn)
    {Γ : Set PropT}
    (hAbs : Absorbable Provable Γ)
    (hW : FrontierWitness Provable K Machine encode_halt Γ) :
    Γ ⊂ F Provable K Machine encode_halt Cn Γ := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hUnion : p ∈ (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := Or.inl hp
    have hCn : p ∈ Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) :=
      (hCnExt (Γ ∪ S1Rel Provable K Machine encode_halt Γ)) hUnion
    simpa [F] using hCn
  · intro hContra
    have hEq : F Provable K Machine encode_halt Cn Γ = Γ := by
      ext p
      constructor
      · exact fun hpF => hContra hpF
      · intro hpΓ
        have hUnion : p ∈ (Γ ∪ S1Rel Provable K Machine encode_halt Γ) := Or.inl hpΓ
        have hCn : p ∈ Cn (Γ ∪ S1Rel Provable K Machine encode_halt Γ) :=
          (hCnExt (Γ ∪ S1Rel Provable K Machine encode_halt Γ)) hUnion
        simpa [F] using hCn
    exact not_fixpoint_F_of_absorbable Provable K Machine encode_halt Cn hCnExt hAbs hW hEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- B') LIFT TO ThState (clean minimal version)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- PostSplitter implies Absorbable (trivial direction). -/
lemma PostSplitter.imp_Absorbable
    {Γ : Set PropT}
    (hPS : PostSplitter Provable Γ) :
    Absorbable Provable Γ := by
  intro p hp
  exact (hPS p).mp hp

/-- Strict step at ThState level. -/
theorem strict_step_state
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A : ThState (PropT := PropT) Provable Cn)
    (hPS : PostSplitter Provable A.Γ)
    (hW : FrontierWitness Provable K Machine encode_halt A.Γ) :
    A.Γ ⊂ (FState Provable K Machine encode_halt Cn hIdem hProvCn A).Γ := by
  have hAbs : Absorbable Provable A.Γ := PostSplitter.imp_Absorbable Provable hPS
  simpa [FState] using strict_F_of_absorbable Provable K Machine encode_halt Cn hCnExt hAbs hW

/-- No fixed point at ThState level. -/
theorem no_fixpoint_state
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A : ThState (PropT := PropT) Provable Cn)
    (hPS : PostSplitter Provable A.Γ)
    (hW : FrontierWitness Provable K Machine encode_halt A.Γ) :
    (FState Provable K Machine encode_halt Cn hIdem hProvCn A).Γ ≠ A.Γ := by
  intro hEq
  have hAbs : Absorbable Provable A.Γ := PostSplitter.imp_Absorbable Provable hPS
  exact not_fixpoint_F_of_absorbable Provable K Machine encode_halt Cn hCnExt hAbs hW
    (by simpa [FState] using hEq)

/-- Strict growth along chainState. -/
theorem strict_chainState_step
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (n : ℕ)
    (hPS : PostSplitter Provable
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ)
    (hW : FrontierWitness Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ
      ⊂
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n+1)).Γ := by
  simpa [chainState_succ] using
    strict_step_state Provable K Machine encode_halt Cn hCnExt hIdem hProvCn
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n) hPS hW

-- ═══════════════════════════════════════════════════════════════════════════════
-- D) GLOBAL DYNAMICS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Global strict growth along the orbit

This block isolates the *two genuinely load-bearing open obligations*:

1) **PostSplitter is preserved by one step**:
   PostSplitter(Γ) → PostSplitter(FState(Γ)).

2) **FrontierWitness is produced automatically at each stage** (from whatever
   "frontier_necessary"/incompleteness hypothesis you use in Complementarity).

Once these two are available, strict growth follows for *all* steps of chainState.
-/

/-- Hypothesis: one-step preservation of PostSplitter along FState. -/
def FState_preserves_PostSplitter
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn) : Prop :=
  ∀ (A : ThState (PropT := PropT) Provable Cn),
    PostSplitter Provable A.Γ →
    PostSplitter Provable (FState Provable K Machine encode_halt Cn hIdem hProvCn A).Γ

/-- Hypothesis: automatic production of a frontier witness at each stage. -/
def FrontierWitness_along_chainState : Prop :=
  ∀ (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn),
    PostSplitter Provable A0.Γ →
    ∀ n, FrontierWitness Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ

/-- PostSplitter propagates along the chain if it is preserved by FState. -/
theorem PostSplitter_chainState
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPSstep : FState_preserves_PostSplitter Provable K Machine encode_halt Cn hIdem hProvCn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hPS0 : PostSplitter Provable A0.Γ) :
    ∀ n, PostSplitter Provable (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ := by
  intro n
  induction n with
  | zero =>
      simpa [chainState] using hPS0
  | succ n ih =>
      have : PostSplitter Provable
          (FState Provable K Machine encode_halt Cn hIdem hProvCn
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n)).Γ :=
        hPSstep _ ih
      simpa [chainState_succ] using this

/--
**Infinite strict growth**: if
- PostSplitter is preserved by FState, and
- FrontierWitness exists at every stage,

then every step is a strict extension: Γ_n ⊂ Γ_{n+1}.
-/
theorem infinite_strict_growth
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPSstep : FState_preserves_PostSplitter Provable K Machine encode_halt Cn hIdem hProvCn)
    (hWchain : FrontierWitness_along_chainState Provable K Machine encode_halt Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hPS0 : PostSplitter Provable A0.Γ) :
    ∀ n,
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ
        ⊂
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n+1)).Γ := by
  intro n
  have hPSn : PostSplitter Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ :=
    PostSplitter_chainState Provable K Machine encode_halt Cn hIdem hProvCn hPSstep A0 hPS0 n
  have hWn : FrontierWitness Provable K Machine encode_halt
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ :=
    hWchain hIdem hProvCn A0 hPS0 n
  exact strict_chainState_step Provable K Machine encode_halt Cn hCnExt hIdem hProvCn A0 n hPSn hWn

-- ═══════════════════════════════════════════════════════════════════════════════
-- C) LIFT TO chainState (dynamic consequences along the orbit)
theorem frontier_nonempty_chainState_of_witnesses
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (HW : ∀ n, FrontierWitness Provable K Machine encode_halt
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ) :
    ∀ n, (S1Rel Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ).Nonempty := by
  intro n
  exact S1Rel_nonempty_of_witness Provable K Machine encode_halt (HW n)


/--
  **Conservation at ThState level**: The frontier is non-empty at each stage
  if it is non-empty for every corpus.
-/
theorem conservation_nonempty_state
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (H : ∀ Γ : Set PropT, (S1Rel Provable K Machine encode_halt Γ).Nonempty) :
    ∀ n, (S1Rel Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ).Nonempty := by
  intro n
  exact H _

/--
  **ω-limit of the chain**: Union of all stages (at the carrier level).
-/
def omegaΓ
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) : Set PropT :=
  { p | ∃ n, p ∈ (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ }

/--
  **Each stage embeds into the ω-limit**.
-/
theorem chainState_le_omegaΓ
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (n : ℕ) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ⊆
    omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 := by
  intro p hp
  exact ⟨n, hp⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- E) ADMISSIBILITY OF OMEGA LIMIT
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Admissibility Condition**:
  A set is Omega-Admissible if it is a fixed point of Cn and is ProvClosed.
-/
def OmegaAdmissible (Provable : Set PropT → PropT → Prop) (Cn : Set PropT → Set PropT) (ωΓ : Set PropT) : Prop :=
  Cn ωΓ = ωΓ ∧ ProvClosed Provable ωΓ

/--
  **Characterization of Membership**:
  A sentence is in ωΓ iff it is in some finite stage.
-/
@[simp] lemma mem_omegaΓ
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) (p : PropT) :
    p ∈ omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0
      ↔ ∃ n, p ∈ (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ := by
  rfl

/-- Step monotonicity (unconditional). -/
theorem chainState_step_hom_def
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (n : ℕ) :
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ⊆
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ := by
  intro p hp
  rw [mem_chainState_succ]
  apply hCnExt
  exact Or.inl hp

/--
  **Chain Monotonicity**:
  The sequence of theory states is increasing w.r.t inclusion.
-/
theorem chainState_mono
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ∀ n m, n ≤ m →
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ⊆
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 m).Γ := by
  intro n m hnm
  induction hnm with
  | refl => exact Subset.refl _
  | step _ ih =>
      exact Subset.trans ih (chainState_step_hom_def Provable K Machine encode_halt Cn hCnExt hIdem hProvCn A0 _)

/--
  **Universal Property (Colimit)**:
  omegaΓ is the smallest set containing all stages.
-/
theorem omegaΓ_universal
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) (T : Set PropT)
    (h : ∀ n, (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ⊆ T) :
    omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 ⊆ T := by
  intro p hp
  rcases hp with ⟨n, hn⟩
  exact h n hn

/--
  **Abstract Directed Provable Closure**:
  Hypothesis: Provability is preserved by directed unions.
-/
def ProvClosedDirected : Prop :=
  ∀ (U : ℕ → Set PropT),
    (∀ n, ProvClosed Provable (U n)) →
    (∀ n, U n ⊆ U (n+1)) →
    ProvClosed Provable {p | ∃ n, p ∈ U n}

/--
  **Admissibility Lemma 1**:
  If ProvClosed is directed-continuous, then omegaΓ is ProvClosed.
-/
theorem omegaΓ_provClosed_of_directed
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (hPCdir : ProvClosedDirected Provable)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ProvClosed Provable (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  refine hPCdir (fun n => (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ) ?_ ?_
  · intro n; exact (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).prov_closed
  · intro n; exact chainState_step_hom_def Provable K Machine encode_halt Cn hCnExt hIdem hProvCn A0 n

/--
  **Abstract Omega-Continuity of Cn**:
  Hypothesis: Deductive closure commutes with directed unions.
-/
def CnOmegaContinuous : Prop :=
  ∀ (U : ℕ → Set PropT),
    (∀ n, U n ⊆ U (n+1)) →
    Cn {p | ∃ n, p ∈ U n} = {p | ∃ n, p ∈ Cn (U n)}

/--
  **Admissibility Lemma 2**:
  If Cn is omega-continuous, then omegaΓ is a fixed point of Cn (Cn-closed).
-/
theorem omegaΓ_cn_closed_of_omega_continuous
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (hω : CnOmegaContinuous Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    Cn (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
      = omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 := by
  -- Monotonicity of the chain
  have hmono : ∀ n, (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ ⊆
                    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n+1)).Γ :=
    fun n => chainState_step_hom_def Provable K Machine encode_halt Cn hCnExt hIdem hProvCn A0 n

  -- Apply continuity
  simp [omegaΓ]
  rw [hω _ hmono] -- Explicit rewrite as simp might not pick it up correctly with arguments

  -- Use that each stage is Cn-closed
  ext p
  constructor <;> intro hp
  · rcases hp with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [(chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).cn_closed] using hn
  · rcases hp with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [(chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).cn_closed] using hn

/--
  **The Admissibility Theorem**:
  Under structural continuity assumptions, the omega-limit is an admissible theory state.
-/
theorem omegaΓ_OmegaAdmissible
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (hPCdir : ProvClosedDirected Provable)
    (hω : CnOmegaContinuous Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    OmegaAdmissible Provable Cn (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  refine ⟨?_, ?_⟩
  · exact omegaΓ_cn_closed_of_omega_continuous Provable K Machine encode_halt Cn hCnExt hIdem hProvCn hω A0
  · exact omegaΓ_provClosed_of_directed Provable K Machine encode_halt Cn hCnExt hIdem hProvCn hPCdir A0

-- ═══════════════════════════════════════════════════════════════════════════════
-- D') OMEGA LIMIT ANALYSIS: The ω-Collapse Phenomenon
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The ω-Collapse Theorem

This section formalizes a key ordinal phenomenon:

**If stage 1 is absorbable, then S1Rel(omegaΓ) = ∅**.

This is the "ω-collapse" effect:
- At finite stages, S1Rel can remain nonempty (frontiers are generated and added).
- But at the limit ω, if absorption holds, *everything that was ever a frontier*
  has been pushed into a successor stage and became provable.
- Hence nothing can remain "kit-certified but unprovable" at ω.

Combined with Route II/T2 (which says S1 must be nonempty for admissible Γ),
this forces a **trilemma**:
1. Absorbable/PostSplitter does NOT propagate along the chain, OR
2. ωΓ is NOT an admissible state (exits ThState or Route II hypotheses), OR
3. The colimit/union is NOT the right limit object (F is not ω-continuous).
-/

/--
  **ω-Collapse Theorem**: If stage 1 along the chain is absorbable, then the
  dynamic frontier at the ω-limit is forced empty.

  This is a fundamental ordinal phenomenon: what "remains unprovable at ω"
  has already been absorbed at a finite stage (hence provable at ω by monotonicity).

  NOTE: This requires only `Absorbable` at stage 1, not at all stages.
-/
theorem S1Rel_omegaΓ_eq_empty_of_absorbable_succ
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hAbs1 :
      Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ) :
    S1Rel Provable K Machine encode_halt
      (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases hp with ⟨e, rfl, hKit, hNprovω⟩

  -- inclusions into ω
  have hIncl0 :
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ ⊆
      omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 :=
    chainState_le_omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 0

  have hIncl1 :
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ ⊆
      omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 :=
    chainState_le_omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0 1

  -- ¬Provable ω ⟹ ¬Provable Γ₀ (contrapositive of monotonicity)
  have hNprov0 :
      ¬ Provable
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ
          (encode_halt e) := by
    intro hP0
    have hPω := hMono _ _ hIncl0 _ hP0
    exact hNprovω hPω

  -- So encode_halt e ∈ S1Rel(Γ₀)
  have hpS1_0 :
      encode_halt e ∈
        S1Rel Provable K Machine encode_halt
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ :=
    ⟨e, rfl, hKit, hNprov0⟩

  -- p ∈ Γ₁ via CnExtensive on the union Γ₀ ∪ S1Rel(Γ₀)
  have hpIn1 :
      encode_halt e ∈
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ := by
    have hUnion : encode_halt e ∈
        ((chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ ∪
          S1Rel Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ) :=
      Or.inr hpS1_0
    have hCnMem : encode_halt e ∈
        Cn ((chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ ∪
          S1Rel Provable K Machine encode_halt
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 0).Γ) :=
      (hCnExt _) hUnion
    -- chainState 1 = FState (chainState 0), and (FState A).Γ = Cn(A.Γ ∪ S1Rel A.Γ)
    simpa [chainState, FState, F] using hCnMem

  -- Absorbable at stage 1: membership ⟹ provability
  have hP1 :
      Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
        (encode_halt e) :=
    hAbs1 _ hpIn1

  -- Monotonicity: Provable Γ₁ ⟹ Provable ωΓ
  have hPω := hMono _ _ hIncl1 _ hP1

  -- Contradiction with ¬Provable ωΓ
  exact hNprovω hPω

/--
  **Trilemma at ω**: If the ω-limit is admissible AND Route II applies,
  then Absorbable cannot hold at stage 1.

  This formalizes the structural constraint:
  - Route II says S1 must be nonempty for admissible Γ.
  - The ω-collapse says Absorbable at stage 1 forces S1(ωΓ) = ∅.
  - Therefore, under Route II, Absorbable cannot hold at stage 1.
-/
theorem omega_trilemma
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    -- Route II hypothesis: S1 is nonempty at ω (the limit is admissible)
    (hRouteII : (S1Rel Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)).Nonempty) :
    ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ := by
  intro hAbs1
  have hEmpty :=
    S1Rel_omegaΓ_eq_empty_of_absorbable_succ Provable K Machine encode_halt Cn
      hMono hCnExt hIdem hProvCn A0 hAbs1
  rw [hEmpty] at hRouteII
  exact Set.not_nonempty_empty hRouteII

-- ═══════════════════════════════════════════════════════════════════════════════
-- D'') TRILEMMA IN DISJUNCTION FORM
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The ω-Trilemma: Explicit Disjunction

We now define intrinsic notions of admissibility and Route II at ω,
then express the trilemma as an explicit disjunction:

    ¬Absorbable(Γ₁) ∨ ¬OmegaAdmissible(ωΓ) ∨ ¬RouteIIAt(ωΓ)

This says: you cannot have all three simultaneously.
At least one must fail for the dynamics to be consistent.
-/



/-- Minimal "Route II at ω" predicate: frontier nonempty.
    This is the condition that Route II/T2 would enforce for admissible states. -/
def RouteIIAt (ωΓ : Set PropT) : Prop :=
  (S1Rel Provable K Machine encode_halt ωΓ).Nonempty

/--
  **Route II Hypotheses**: The conditions under which Route II applies.
  This bundles Soundness + Negative Completeness + the T2 barrier.
  When these hold AND the state is OmegaAdmissible, then RouteIIAt is forced.
-/
structure RouteIIHyp' (SProvable : PropT → Prop) (SNot : PropT → PropT) (ωΓ : Set PropT) : Prop where
  soundness : ∀ p, Provable ωΓ p → SProvable p
  negComplete : ∀ e : Code, ¬ Rev0_K K (Machine e) → SProvable (SNot (encode_halt e))
  barrier : (∀ e, SProvable (encode_halt e) ∨ SProvable (SNot (encode_halt e))) → False

/--
  **Route II applies to admissible states**: The key coupling.
  If ωΓ is admissible (in the intrinsic sense), then Route II forces S1 nonempty.
  This is the bridge that makes the trilemma genuinely 3-way.
-/
def RouteIIApplies (ωΓ : Set PropT) : Prop :=
  OmegaAdmissible Provable Cn ωΓ → (S1Rel Provable K Machine encode_halt ωΓ).Nonempty

/--
  **Trilemma in Disjunction Form**: All three branches are active.

  This version properly uses OmegaAdmissible by splitting on all cases.
  The trilemma says: given Absorbable(Γ₁) and OmegaAdmissible(ωΓ),
  we can derive ¬RouteIIAt(ωΓ).
-/
theorem omega_trilemma_disjunction
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
    ∨ ¬ OmegaAdmissible Provable Cn
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
    ∨ ¬ RouteIIAt Provable K Machine encode_halt
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := by
  classical
  by_cases hAbs :
      Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
  · by_cases hΩ :
        OmegaAdmissible Provable Cn
          (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
    · -- Both Absorbable and OmegaAdmissible hold → Route II must fail
      right; right
      intro hR
      -- Use omega_trilemma directly: RouteIIAt → ¬Absorbable, contradiction
      have hNAbs := omega_trilemma Provable K Machine encode_halt Cn
          hMono hCnExt hIdem hProvCn A0 hR
      exact hNAbs hAbs
    · -- OmegaAdmissible fails
      right; left; exact hΩ
  · -- Absorbable fails
    left; exact hAbs

/--
  **Trilemma (Conjunction Form)**: It is impossible to have all three conditions.

  This is often more exploitable: given any two, you can derive the negation of the third.
-/
theorem omega_trilemma_not_all
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ¬ (Absorbable Provable
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ
       ∧ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)
       ∧ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) := by
  intro h
  have hR : RouteIIAt Provable K Machine encode_halt
      (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) := h.2.2
  have hNAbs :=
    omega_trilemma Provable K Machine encode_halt Cn
      hMono hCnExt hIdem hProvCn A0 hR
  exact hNAbs h.1

/--
  **Structural Corollary**: If Route II applies to all admissible states,
  then Absorbable + OmegaAdmissible → False.

  This is the "pure structural" form: the dynamics cannot have both
  successor-level absorption and limit-level admissibility when Route II holds.
-/
theorem omega_collapse_structural
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hRouteIIApplies : RouteIIApplies Provable K Machine encode_halt Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0))
    (hAbs : Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 1).Γ)
    (hΩ : OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0)) :
    False := by
  have hR : RouteIIAt Provable K Machine encode_halt
      (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn A0) :=
    hRouteIIApplies hΩ
  exact (omega_trilemma_not_all Provable K Machine encode_halt Cn
    hMono hCnExt hIdem hProvCn A0) ⟨hAbs, hΩ, hR⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- E) BRIDGE TO COMPLEMENTARITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Connecting to frontier_necessary from Complementarity

The abstract hypotheses `FState_preserves_PostSplitter` and `FrontierWitness_along_chainState`
can be instantiated using theorems from `Complementarity.lean`, specifically:

1. **frontier_necessary** proves `(S1Eff S encode_halt).Nonempty` under negative completeness
   and semi-decidability assumptions.

2. `S1Eff.Nonempty` implies `FrontierWitness` because both capture the same concept:
   ∃ e, Rev0_K K (Machine e) ∧ ¬ Provable Γ (encode_halt e).

The following theorem makes this connection explicit.
-/

/--
  **S1Rel.Nonempty implies FrontierWitness** (definitional equivalence).
  This shows that `S1Rel Γ ≠ ∅` is the same as having a `FrontierWitness` for Γ.
-/
theorem FrontierWitness_of_S1Rel_nonempty
    {Γ : Set PropT}
    (h : (S1Rel Provable K Machine encode_halt Γ).Nonempty) :
    FrontierWitness Provable K Machine encode_halt Γ := by
  rcases h with ⟨p, hp⟩
  rcases hp with ⟨e, hpEq, hKit, hNprov⟩
  exact ⟨e, hKit, hNprov⟩

/--
  **FrontierWitness implies S1Rel.Nonempty** (converse direction).
-/
theorem S1Rel_nonempty_of_FrontierWitness
    {Γ : Set PropT}
    (h : FrontierWitness Provable K Machine encode_halt Γ) :
    (S1Rel Provable K Machine encode_halt Γ).Nonempty := by
  rcases h with ⟨e, hKit, hNprov⟩
  refine ⟨encode_halt e, ?_⟩
  exact ⟨e, rfl, hKit, hNprov⟩

/--
  **S1Rel.Nonempty ↔ FrontierWitness** (definitional equivalence).
-/
theorem S1Rel_nonempty_iff_FrontierWitness
    {Γ : Set PropT} :
    (S1Rel Provable K Machine encode_halt Γ).Nonempty ↔
    FrontierWitness Provable K Machine encode_halt Γ :=
  ⟨FrontierWitness_of_S1Rel_nonempty Provable K Machine encode_halt,
   S1Rel_nonempty_of_FrontierWitness Provable K Machine encode_halt⟩

/-!
### How to instantiate the global dynamics

To apply `infinite_strict_growth` to a concrete `ComplementaritySystem S`, you would:

1. Set `Provable := S.Provable`, `K := S.K`, `Machine := S.Machine ∘ S.dec`, `encode_halt := your_encoding`
2. Prove `FState_preserves_PostSplitter` for your specific `Cn` (usually `Cn = id` or a sound closure)
3. Use `frontier_necessary` to derive `S1Rel.Nonempty` for each stage, then convert to `FrontierWitness`
   via `FrontierWitness_of_S1Rel_nonempty`

This completes the bridge between the abstract dynamics and the concrete impossibility theorems.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
end Functor
end RevHalt
