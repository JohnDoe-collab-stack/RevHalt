import RevHalt.Bridge.Context
import RevHalt.Kinetic.Closure
import RevHalt.Kinetic.MasterClosure
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Kinetic.Stratification

Stratified dynamic gaps and the "for each → for all" reduction.

## Key Insight

In this framework, `Truth = CloK ∅` extensionally (via `h_bridge` + `Truth_is_CloK`).
The gap `CloK ∅ \ ProvableSet` is non-empty by `Master_Closure`.

This module introduces a **stratification by stages**: iterating `CloK` over
growing contexts produces a chain `Chain(n)`, whose union `MasterClo` may cover
the entire proposition space. When it does, we obtain global truth.

## Contents
- Dynamic hypotheses: `LRMonotone`, `LRRefl`, `ContextSound`
- Stratification: `Chain`, `MasterClo`, `NewLayer`, `GapLayer`
- Structural lemmas: `Next_mono`, `Chain_mono_succ`, `Chain_truth`
- Gap lemmas: `BaseGap_nonempty`, `GapLayer0_nonempty`
- Master theorem: `Truth_for_all_of_MasterClo_univ`
-/

namespace RevHalt

open Set

namespace Kinetic

variable {Code PropT : Type}

-- ============================================================================
-- 1) Dynamic Hypotheses
-- ============================================================================

/--
**LRMonotone**: Adding hypotheses doesn't break verification.

If a proposition is verifiable at time `t` under context `Γ`, it remains
verifiable at time `t` under any larger context `Γ'`.

This is used to prove monotonicity of the `Next` operator.
-/
def LRMonotone (ctx : VerifiableContext Code PropT) : Prop :=
  ∀ ⦃Γ Γ' : Set PropT⦄ ⦃p : PropT⦄ ⦃t : ℕ⦄,
    Γ ⊆ Γ' → ctx.LR Γ p t → ctx.LR Γ' p t

/--
**LRRefl**: Hypotheses are immediately available.

If `p` is in context `Γ`, then the trace `LR Γ p` halts (p is trivially verifiable).

This is used to prove accumulation: `Chain n ⊆ Chain (n+1)`.
-/
def LRRefl (ctx : VerifiableContext Code PropT) : Prop :=
  ∀ ⦃Γ : Set PropT⦄ ⦃p : PropT⦄, p ∈ Γ → Halts (ctx.LR Γ p)

/--
**ContextSound**: Soundness under context (one direction only).

If all hypotheses in `Γ` are true, and if `LR Γ p` halts, then `p` is true.

Note: This gives only `AssumptionsTrue Γ → Halts(LR Γ p) → Truth p`,
NOT the full `Truth p ↔ Halts(LR Γ p)` for non-empty Γ.
It is the key hypothesis for propagating truth through stages.
-/
def ContextSound (ctx : VerifiableContext Code PropT) : Prop :=
  ∀ (Γ : Set PropT) (p : PropT),
    (∀ ψ, ψ ∈ Γ → ctx.Truth ψ) →
    Halts (ctx.LR Γ p) →
    ctx.Truth p

-- ============================================================================
-- 2) Stratification Definitions
-- ============================================================================

/-- One step of iteration: `Γ ↦ CloK(Γ)`. -/
def Next (ctx : VerifiableContext Code PropT) (Γ : Set PropT) : Set PropT :=
  CloK (LR := ctx.LR) Γ

/--
**Chain**: The master chain of stages.

- `Chain 0 = ∅`
- `Chain (n+1) = CloK(Chain n)`

Each stage accumulates what is kinetically verifiable from the previous stage.
-/
def Chain (ctx : VerifiableContext Code PropT) : ℕ → Set PropT
  | 0 => ∅
  | n + 1 => Next ctx (Chain ctx n)

/--
**MasterClo**: The master closure.

Defined as `{ p | ∃ n, p ∈ Chain n }`, which is extensionally equal to `⋃ n, Chain n`.

If `MasterClo = univ`, then every proposition is reached by some stage.
-/
def MasterClo (ctx : VerifiableContext Code PropT) : Set PropT :=
  { p | ∃ n, p ∈ Chain ctx n }

/--
**NewLayer**: What emerges at stage `n+1` (delta).

`NewLayer n = Chain (n+1) \ Chain n`

These are propositions that become kinetically verifiable at stage `n+1`
but were NOT verifiable at stage `n`.
-/
def NewLayer (ctx : VerifiableContext Code PropT) (n : ℕ) : Set PropT :=
  Chain ctx (n+1) \ Chain ctx n

/--
**GapLayer**: The gap at stage `n` (emergence minus provables).

`GapLayer n = NewLayer n \ ProvableSet`

These are propositions that EMERGE at stage `n+1` (new delta)
and are not formally provable.
-/
def GapLayer (ctx : VerifiableContext Code PropT) (n : ℕ) : Set PropT :=
  NewLayer ctx n \ ProvableSet ctx.toEnrichedContext

/--
**BaseGap**: The cumulative gap at CloK ∅ (for compatibility).

`BaseGap = Chain 1 \ ProvableSet = CloK ∅ \ ProvableSet`
-/
def BaseGap (ctx : VerifiableContext Code PropT) : Set PropT :=
  Chain ctx 1 \ ProvableSet ctx.toEnrichedContext

-- ============================================================================
-- 3) Convenience Lemmas
-- ============================================================================

@[simp] theorem Chain_zero (ctx : VerifiableContext Code PropT) :
    Chain ctx 0 = ∅ := rfl

@[simp] theorem Chain_succ (ctx : VerifiableContext Code PropT) (n : ℕ) :
    Chain ctx (n+1) = Next ctx (Chain ctx n) := rfl

theorem mem_MasterClo_iff (ctx : VerifiableContext Code PropT) (p : PropT) :
    p ∈ MasterClo ctx ↔ ∃ n, p ∈ Chain ctx n := Iff.rfl

theorem mem_NewLayer_iff (ctx : VerifiableContext Code PropT) (n : ℕ) (p : PropT) :
    p ∈ NewLayer ctx n ↔ p ∈ Chain ctx (n+1) ∧ p ∉ Chain ctx n := Iff.rfl

theorem mem_GapLayer_iff (ctx : VerifiableContext Code PropT) (n : ℕ) (p : PropT) :
    p ∈ GapLayer ctx n ↔ p ∈ NewLayer ctx n ∧ p ∉ ProvableSet ctx.toEnrichedContext := Iff.rfl

theorem mem_BaseGap_iff (ctx : VerifiableContext Code PropT) (p : PropT) :
    p ∈ BaseGap ctx ↔ p ∈ Chain ctx 1 ∧ p ∉ ProvableSet ctx.toEnrichedContext := Iff.rfl

-- ============================================================================
-- 4) Structural Lemmas
-- ============================================================================

/--
**Next is monotone** (under `LRMonotone`).

If `Γ ⊆ Γ'`, then `Next Γ ⊆ Next Γ'`.
-/
theorem Next_mono (ctx : VerifiableContext Code PropT)
    (hmono : LRMonotone ctx) : Monotone (Next ctx) := by
  intro Γ Γ' hsub p hp
  rw [Next, mem_CloK_iff_exists_time] at hp ⊢
  rcases hp with ⟨t, ht⟩
  exact ⟨t, hmono hsub ht⟩

/--
**Chain is accumulating** (under `LRRefl`).

`Chain n ⊆ Chain (n+1)` for all `n`.
-/
theorem Chain_mono_succ (ctx : VerifiableContext Code PropT)
    (hrefl : LRRefl ctx) : ∀ n, Chain ctx n ⊆ Chain ctx (n+1) := by
  intro n p hp
  rw [Chain_succ, Next, mem_CloK_iff]
  exact hrefl hp

/--
**Chain is monotone in indices** (under `LRRefl`).
-/
theorem Chain_mono (ctx : VerifiableContext Code PropT)
    (hrefl : LRRefl ctx) : Monotone (Chain ctx) := by
  intro n m hnm
  induction hnm with
  | refl => exact fun p hp => hp
  | step _ ih => exact fun p hp => Chain_mono_succ ctx hrefl _ (ih hp)

/--
**The base gap is non-empty** (under soundness).

Uses `Master_Closure` to obtain a witness in `CloK ∅ \ ProvableSet`.
-/
theorem BaseGap_nonempty
    (ctx : VerifiableContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∃ p, p ∈ BaseGap ctx := by
  have h := Master_Closure (ctx := ctx) (h_sound := h_sound)
  rcases h.2 with ⟨p, hpCloK, hpNotProv⟩
  refine ⟨p, ?_⟩
  have hpChain1 : p ∈ Chain ctx 1 := by
    rw [Chain_succ, Next]
    exact hpCloK
  exact ⟨hpChain1, hpNotProv⟩

/--
**NewLayer 0 equals Chain 1** (since Chain 0 = ∅).
-/
theorem NewLayer0_eq_Chain1 (ctx : VerifiableContext Code PropT) :
    NewLayer ctx 0 = Chain ctx 1 := by
  ext p
  simp only [NewLayer, Chain_zero]
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, fun h' => h'⟩

/--
**GapLayer 0 equals BaseGap** (since NewLayer 0 = Chain 1).
-/
theorem GapLayer0_eq_BaseGap (ctx : VerifiableContext Code PropT) :
    GapLayer ctx 0 = BaseGap ctx := by
  ext p
  simp only [GapLayer, NewLayer, BaseGap, Chain_zero]
  constructor
  · intro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩; exact ⟨⟨h1, fun h' => h'⟩, h2⟩

theorem GapLayer0_nonempty
    (ctx : VerifiableContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∃ p, p ∈ GapLayer ctx 0 := by
  rw [GapLayer0_eq_BaseGap]
  exact BaseGap_nonempty ctx h_sound

/--
**All stages are true** (under `ContextSound`).

By induction: `Chain 0 = ∅` is trivially true, and if `Chain n` is true,
then `Chain (n+1) = CloK(Chain n)` is true by `ContextSound`.
-/
theorem Chain_truth (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx) :
    ∀ n, ∀ p, p ∈ Chain ctx n → ctx.Truth p := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp [Chain] at hp
  | succ n ih =>
      intro p hp
      rw [Chain_succ, Next, mem_CloK_iff] at hp
      exact hCS (Chain ctx n) p ih hp

-- ============================================================================
-- 5) Master Theorem
-- ============================================================================

/--
**Master Theorem: Coverage implies global truth.**

If `ContextSound` holds and `MasterClo = univ`, then every proposition is true.

This is the "for each → for all" reduction: if the stratified chain covers
all propositions, and each stage preserves truth, then all is true.
-/
theorem Truth_for_all_of_MasterClo_univ
    (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx)
    (hcover : MasterClo ctx = (Set.univ : Set PropT)) :
    ∀ p : PropT, ctx.Truth p := by
  intro p
  have hp : p ∈ MasterClo ctx := by rw [hcover]; exact Set.mem_univ p
  rw [mem_MasterClo_iff] at hp
  rcases hp with ⟨n, hn⟩
  exact Chain_truth ctx hCS n p hn

-- ============================================================================
-- 6) NewLayer / GapLayer Properties (structural)
-- ============================================================================

/--
**NewLayer partitions the growth** (under LRRefl).

Elements in Chain (n+1) are either from Chain n or from NewLayer n.
-/
theorem Chain_succ_eq_union_NewLayer (ctx : VerifiableContext Code PropT)
    (hrefl : LRRefl ctx) (n : ℕ) :
    Chain ctx (n+1) = Chain ctx n ∪ NewLayer ctx n := by
  ext p
  simp only [NewLayer, Set.mem_union, Set.mem_diff]
  constructor
  · intro hp
    by_cases h : p ∈ Chain ctx n
    · left; exact h
    · right; exact ⟨hp, h⟩
  · intro hp
    rcases hp with h | ⟨h, _⟩
    · exact Chain_mono_succ ctx hrefl n h
    · exact h

/--
**MasterClo is the union over all NewLayers plus base** (under LRRefl).

Note: Since Chain 0 = ∅, the base term is vacuous, so:
`MasterClo = { p | ∃ n, p ∈ NewLayer n }`
-/
theorem MasterClo_eq_union_NewLayers (ctx : VerifiableContext Code PropT)
    (_ : LRRefl ctx) :
    MasterClo ctx = { p | ∃ n, p ∈ NewLayer ctx n } := by
  ext p
  constructor
  · -- MasterClo → NewLayers
    intro ⟨n, hn⟩
    -- Use strong induction: find the FIRST stage where p appears
    induction n with
    | zero =>
        -- Chain 0 = ∅, so p ∈ Chain 0 is impossible
        simp [Chain] at hn
    | succ m ih =>
        by_cases h : p ∈ Chain ctx m
        · -- p was already in Chain m, apply induction
          exact ih h
        · -- p is NOT in Chain m but IS in Chain (m+1): emergence!
          exact ⟨m, hn, h⟩
  · -- NewLayers → MasterClo
    intro ⟨n, hn, _⟩
    exact ⟨n + 1, hn⟩

end Kinetic

end RevHalt
