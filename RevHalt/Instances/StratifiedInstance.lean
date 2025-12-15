import RevHalt.Kinetic.Stratification
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# RevHalt.Instances.StratifiedInstance

Gap-Cover via Dynamic Propagation.

## Key Structural Facts (non-degenerate)

1. `Chain1_eq_TruthSet` : Chain 1 = TruthSet (via bridge)
2. `MasterClo_eq_TruthSet` : MasterClo = TruthSet (chain stabilizes, under ContextSound)
3. `BaseGap_eq_MasterClo_diff_Provable` : BaseGap = MasterClo \ ProvableSet
4. `ProvableSet_ssubset_MasterClo` : ProvableSet ⊂ MasterClo (from h_sound + T2)

## Gap as Engine (the real dynamic mechanism)

T2 gives a gap witness, but doesn't give propagation.
For gap → coverage, we need a **propagation property** of LR:

`LRPropagates`: From any gap element, LR can reach all propositions.

This is the real minimal hypothesis for `gap_drives_cover`.
-/

namespace RevHalt

namespace Kinetic

open Set

variable {Code PropT : Type}

-- ============================================================================
-- Section 1: Core Structural Lemmas
-- ============================================================================

/--
**Chain 1 equals TruthSet** (via bridge).

This is the fundamental bridge between kinetic dynamics and semantics.
At stage 1, CloK(∅) captures exactly the true propositions.
-/
theorem Chain1_eq_TruthSet (ctx : VerifiableContext Code PropT) :
    Chain ctx 1 = { p | ctx.Truth p } := by
  ext p
  simp only [Chain_succ, Chain_zero, Next, mem_CloK_iff, Set.mem_setOf_eq]
  exact (ctx.h_bridge p).symm

/--
**MasterClo equals TruthSet** (chain stabilizes).

Under ContextSound:
- By Chain_truth: all elements in Chain n are true
- By Chain1_eq_TruthSet: all truths are in Chain 1
- Therefore MasterClo = TruthSet
-/
theorem MasterClo_eq_TruthSet
    (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx) :
    MasterClo ctx = { p | ctx.Truth p } := by
  ext p
  constructor
  · intro ⟨n, hn⟩
    exact Chain_truth ctx hCS n p hn
  · intro hTruth
    use 1
    rw [Chain1_eq_TruthSet]
    exact hTruth

/--
**MasterClo = univ iff all are true** (fundamental equivalence).
-/
theorem MasterClo_univ_iff_all_true
    (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx) :
    MasterClo ctx = univ ↔ (∀ p, ctx.Truth p) := by
  rw [MasterClo_eq_TruthSet ctx hCS]
  constructor
  · intro h p
    have : p ∈ { q | ctx.Truth q } := by rw [h]; exact mem_univ p
    exact this
  · intro h
    ext p
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact h p

/--
**BaseGap characterization**: true-but-unprovable.
-/
theorem mem_BaseGap_iff_truth_not_provable (ctx : VerifiableContext Code PropT) (p : PropT) :
    p ∈ BaseGap ctx ↔ ctx.Truth p ∧ ¬ctx.Provable p := by
  rw [mem_BaseGap_iff]
  constructor
  · intro ⟨hChain1, hNotProv⟩
    have hTruth : ctx.Truth p := by rw [Chain1_eq_TruthSet] at hChain1; exact hChain1
    exact ⟨hTruth, hNotProv⟩
  · intro ⟨hTruth, hNotProv⟩
    exact ⟨by rw [Chain1_eq_TruthSet]; exact hTruth, hNotProv⟩

-- ============================================================================
-- Section 2: Key Structural Identities
-- ============================================================================

/--
**BaseGap equals MasterClo minus ProvableSet** (under ContextSound).

This is the fundamental identity connecting gap and coverage:
the gap is exactly what MasterClo adds beyond ProvableSet.
-/
theorem BaseGap_eq_MasterClo_diff_Provable
    (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx) :
    BaseGap ctx = MasterClo ctx \ ProvableSet ctx.toEnrichedContext := by
  ext p
  rw [mem_BaseGap_iff_truth_not_provable, MasterClo_eq_TruthSet ctx hCS]
  simp only [mem_diff, mem_setOf_eq]
  rfl

/--
**ProvableSet is strictly contained in MasterClo** (under hCS + h_sound).

This is a genuine structural fact:
- h_sound gives ProvableSet ⊆ TruthSet = MasterClo
- T2 gives a witness in TruthSet \ ProvableSet
- Therefore the inclusion is strict
-/
theorem ProvableSet_ssubset_MasterClo
    (ctx : VerifiableContext Code PropT)
    (hCS : ContextSound ctx)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ProvableSet ctx.toEnrichedContext ⊂ MasterClo ctx := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro q hq
    rw [MasterClo_eq_TruthSet ctx hCS, mem_setOf_eq]
    exact h_sound q hq
  · intro heq
    obtain ⟨p, hT, hNP⟩ := true_but_unprovable_exists ctx.toEnrichedContext
    have h1 : p ∈ MasterClo ctx := by rw [MasterClo_eq_TruthSet ctx hCS]; exact hT
    have h2 : p ∉ ProvableSet ctx.toEnrichedContext := hNP
    rw [← heq] at h1
    exact h2 h1

/--
**Gap always exists** (from T2, no extra hypothesis needed).
-/
theorem gap_always_exists (ctx : VerifiableContext Code PropT) :
    ∃ p, p ∈ BaseGap ctx := by
  obtain ⟨p, hT, hNP⟩ := true_but_unprovable_exists ctx.toEnrichedContext
  use p
  rw [mem_BaseGap_iff_truth_not_provable]
  exact ⟨hT, hNP⟩

-- ============================================================================
-- Section 3: Propagation Property (The Real Dynamic Hypothesis)
-- ============================================================================

/--
**LRPropagatesFromGap**: The correct propagation property of LR.

This says: from any gap element g **as hypothesis**, every proposition becomes reachable.
The key is that LR uses `{g}` as context, NOT `∅`.

This is NOT equivalent to the bridge (which only talks about `∅`):
- Bridge: `Halts (LR ∅ p) ↔ Truth p`
- LRPropagatesFromGap: `Halts (LR {g} p)` for all p, given g in gap

The gap serves as "fuel": from a witness g available as hypothesis,
the dynamics can reach any proposition p.
-/
def LRPropagatesFromGap (ctx : VerifiableContext Code PropT) : Prop :=
  ∀ g, g ∈ BaseGap ctx → ∀ p, Halts (ctx.LR ({g} : Set PropT) p)

-- ============================================================================
-- Section 4: Gap Drives Cover (The Main Theorem)
-- ============================================================================

/--
**gap_drives_cover**: The gap drives coverage under LRPropagatesFromGap.

Under the propagation hypothesis:
1. Gap exists (from T2): ∃ g ∈ BaseGap
2. LRPropagatesFromGap: g ∈ BaseGap → ∀ p, Halts (LR {g} p)
3. Under ContextSound: if g is true (which it is, since g ∈ BaseGap ⊆ TruthSet)
   and Halts (LR {g} p), then Truth p
4. Therefore ∀ p, Truth p
5. Therefore MasterClo = univ

This is the "for each → for all" reduction with the correct non-circular hypothesis.
-/
theorem gap_drives_cover
    (ctx : VerifiableContext Code PropT)
    (_ : LRMonotone ctx)
    (_ : LRRefl ctx)
    (hCS : ContextSound ctx)
    (_ : ∀ p, ctx.Provable p → ctx.Truth p)
    (hProp : LRPropagatesFromGap ctx) :
    (∃ g, g ∈ BaseGap ctx) → MasterClo ctx = univ := by
  intro ⟨g, hg⟩
  -- g is in BaseGap, so g is true (BaseGap ⊆ TruthSet)
  have hgTrue : ctx.Truth g := (mem_BaseGap_iff_truth_not_provable ctx g).mp hg |>.1
  -- From LRPropagatesFromGap: g ∈ BaseGap → ∀ p, Halts (LR {g} p)
  have hAllHalt : ∀ p, Halts (ctx.LR ({g} : Set PropT) p) := hProp g hg
  -- Under ContextSound: if all of {g} are true and Halts (LR {g} p), then Truth p
  have hAllTrue : ∀ p, ctx.Truth p := fun p => by
    apply hCS ({g} : Set PropT) p
    · intro ψ hψ
      have : ψ = g := by
        simpa [mem_singleton_iff] using hψ
      simpa [this] using hgTrue
    · exact hAllHalt p
  -- ∀ p, Truth p → MasterClo = univ
  exact (MasterClo_univ_iff_all_true ctx hCS).mpr hAllTrue

/--
**Corollary**: Under propagation, gap ↔ coverage.

Note: The (←) direction is trivial (gap always exists by T2).
The (→) direction requires the propagation hypothesis.
-/
theorem gap_iff_cover_with_propagation
    (ctx : VerifiableContext Code PropT)
    (hmono : LRMonotone ctx)
    (hrefl : LRRefl ctx)
    (hCS : ContextSound ctx)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p)
    (hProp : LRPropagatesFromGap ctx) :
    (∃ p, p ∈ BaseGap ctx) ↔ MasterClo ctx = univ := by
  constructor
  · exact gap_drives_cover ctx hmono hrefl hCS h_sound hProp
  · intro _; exact gap_always_exists ctx

-- ============================================================================
-- Section 5: Summary of Structural Facts
-- ============================================================================

/--
**Main structural theorem**: summarizes all non-degenerate relationships.

Under the standard hypotheses:
1. Gap always exists (from T2)
2. MasterClo = TruthSet (chain stabilizes)
3. BaseGap = MasterClo \ ProvableSet (gap is the excess)
4. ProvableSet ⊂ MasterClo (strict inclusion)
-/
theorem gap_cover_structural_facts
    (ctx : VerifiableContext Code PropT)
    (_ : LRMonotone ctx)
    (_ : LRRefl ctx)
    (hCS : ContextSound ctx)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    -- (1) Gap always exists (from T2)
    (∃ p, p ∈ BaseGap ctx) ∧
    -- (2) MasterClo = TruthSet
    (MasterClo ctx = { p | ctx.Truth p }) ∧
    -- (3) BaseGap = MasterClo \ ProvableSet
    (BaseGap ctx = MasterClo ctx \ ProvableSet ctx.toEnrichedContext) ∧
    -- (4) ProvableSet ⊂ MasterClo (strict inclusion)
    (ProvableSet ctx.toEnrichedContext ⊂ MasterClo ctx) := by
  exact ⟨gap_always_exists ctx,
         MasterClo_eq_TruthSet ctx hCS,
         BaseGap_eq_MasterClo_diff_Provable ctx hCS,
         ProvableSet_ssubset_MasterClo ctx hCS h_sound⟩

end Kinetic

end RevHalt
