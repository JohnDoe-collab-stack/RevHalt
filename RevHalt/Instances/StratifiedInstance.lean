import RevHalt.Kinetic.Stratification
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Instances.StratifiedInstance

A complete instance demonstrating the full stratification pipeline
where the **gap is STRICTLY the only driver** of coverage.

## Key Design: Gap as Explicit Hypothesis

To prove "gap is indispensable", we:
1. Define `PreVerifiableContext` (weaker than `VerifiableContext`, no T2)
2. Make the gap a **hypothesis** (not a theorem)
3. Prove: hg → MasterClo = univ (sufficiency)
4. Provide counterexample: model without gap where coverage fails (necessity)

This makes "gap-driven" formally provable in both directions.
-/

namespace RevHalt

namespace Instances

open Set

-- ============================================================================
-- PART A: PreVerifiableContext (no T2, gap is hypothesis)
-- ============================================================================

/--
A weaker context structure that does NOT embed T2.
The gap is not forced to exist — it must be given as hypothesis.
-/
structure PreVerifiableContext (PropT : Type) where
  Truth : PropT → Prop
  Provable : PropT → Prop
  Not : PropT → PropT
  LR : Set PropT → PropT → Trace
  h_bridge : ∀ p, Truth p ↔ Halts (LR ∅ p)

variable {PropT : Type}

-- ============================================================================
-- Stratification definitions for PreVerifiableContext
-- ============================================================================

/-- CloK for PreVerifiableContext. -/
def preCloK (ctx : PreVerifiableContext PropT) (Γ : Set PropT) : Set PropT :=
  { p | Halts (ctx.LR Γ p) }

/-- Next layer. -/
def preNext (ctx : PreVerifiableContext PropT) (Γ : Set PropT) : Set PropT :=
  preCloK ctx Γ

/-- Chain of stages. -/
def preChain (ctx : PreVerifiableContext PropT) : ℕ → Set PropT
  | 0 => ∅
  | n + 1 => preNext ctx (preChain ctx n)

/-- Master closure. -/
def preMasterClo (ctx : PreVerifiableContext PropT) : Set PropT :=
  { p | ∃ n, p ∈ preChain ctx n }

/-- ProvableSet. -/
def preProvableSet (ctx : PreVerifiableContext PropT) : Set PropT :=
  { p | ctx.Provable p }

/-- BaseGap. -/
def preBaseGap (ctx : PreVerifiableContext PropT) : Set PropT :=
  preChain ctx 1 \ preProvableSet ctx

/-- Membership lemmas. -/
theorem mem_preChain_succ (ctx : PreVerifiableContext PropT) (n : ℕ) (p : PropT) :
    p ∈ preChain ctx (n + 1) ↔ Halts (ctx.LR (preChain ctx n) p) := Iff.rfl

theorem mem_preMasterClo (ctx : PreVerifiableContext PropT) (p : PropT) :
    p ∈ preMasterClo ctx ↔ ∃ n, p ∈ preChain ctx n := Iff.rfl

-- ============================================================================
-- PART B: The dynamic Step relation
-- ============================================================================

/-- The Step relation: successor OR reset to 0. -/
def Step (n m : ℕ) : Prop := m = n + 1 ∨ m = 0

/-- Reachability via Step (transitive closure). -/
inductive Reach : ℕ → ℕ → Prop where
  | refl : ∀ n, Reach n n
  | step : ∀ n m k, Reach n m → Step m k → Reach n k

/-- From any n, we can reach 0 via reset. -/
theorem reach_zero (n : ℕ) : Reach n 0 :=
  Reach.step n n 0 (Reach.refl n) (Or.inr rfl)

/-- From 0, we can reach any m via successor steps. -/
theorem reach_from_zero : ∀ m : ℕ, Reach 0 m := by
  intro m
  induction m with
  | zero => exact Reach.refl 0
  | succ k ih => exact Reach.step 0 k (k + 1) ih (Or.inl rfl)

-- ============================================================================
-- PART C: DynPreContext (the abstract instance)
-- ============================================================================

/-- Abstract context parameters (axiomatized). -/
axiom DynLR : Set ℕ → ℕ → Trace

axiom DynTruth : ℕ → Prop

axiom DynProvable : ℕ → Prop

/-- Axiom: Nothing is provable. -/
axiom DynProvable_false : ∀ n, ¬ DynProvable n

/-- Axiom: LR Γ n halts iff n ∈ Γ or n is reachable from Γ via Step (for non-empty Γ). -/
axiom DynLR_halts_iff_nonempty (Γ : Set ℕ) (n : ℕ) (hΓ : Γ.Nonempty) :
    Halts (DynLR Γ n) ↔ (n ∈ Γ ∨ ∃ m ∈ Γ, Reach m n)

/-- Axiom: LR halts at empty context iff Truth holds (bridge). -/
axiom DynLR_bridge : ∀ n, DynTruth n ↔ Halts (DynLR ∅ n)

/-- The PreVerifiableContext instance. -/
def DynPreContext : PreVerifiableContext ℕ where
  Truth := DynTruth
  Provable := DynProvable
  Not := fun n => n  -- trivial negation
  LR := DynLR
  h_bridge := DynLR_bridge

-- ============================================================================
-- PART D: Propagation lemmas (gap-driven)
-- ============================================================================

/-- Propagation Reset. -/
theorem pre_propagate_reset (n k : ℕ)
    (hn : n ∈ preChain DynPreContext k) :
    0 ∈ preChain DynPreContext (k + 1) := by
  simp only [preChain, preNext, preCloK, Set.mem_setOf_eq]
  have hΓ : (preChain DynPreContext k).Nonempty := ⟨n, hn⟩
  have hr : Reach n 0 := reach_zero n
  exact (DynLR_halts_iff_nonempty (preChain DynPreContext k) 0 hΓ).2 (Or.inr ⟨n, hn, hr⟩)

/-- Propagation Succ. -/
theorem pre_propagate_succ (n k : ℕ)
    (hn : n ∈ preChain DynPreContext k) :
    n + 1 ∈ preChain DynPreContext (k + 1) := by
  simp only [preChain, preNext, preCloK, Set.mem_setOf_eq]
  have hΓ : (preChain DynPreContext k).Nonempty := ⟨n, hn⟩
  have hr : Reach n (n + 1) := Reach.step n n (n + 1) (Reach.refl n) (Or.inl rfl)
  exact (DynLR_halts_iff_nonempty (preChain DynPreContext k) (n+1) hΓ).2 (Or.inr ⟨n, hn, hr⟩)

-- ============================================================================
-- PART E: Sufficiency — hg → MasterClo = univ
-- ============================================================================

/--
**Main Theorem (Sufficiency)**: If the gap is non-empty, then coverage is universal.

The gap is the driver: from a gap witness, we propagate to all of ℕ.
-/
theorem gap_drives_coverage
    (hg : ∃ n, n ∈ preBaseGap DynPreContext) :
    preMasterClo DynPreContext = Set.univ := by
  -- Extract seed from gap
  rcases hg with ⟨n0, hn0⟩
  have hn0_chain1 : n0 ∈ preChain DynPreContext 1 := hn0.1
  -- 0 ∈ Chain 2 (reset from n0)
  have h0 : 0 ∈ preChain DynPreContext 2 := pre_propagate_reset n0 1 hn0_chain1
  -- All n ∈ Chain by induction
  ext n
  constructor
  · intro _; exact Set.mem_univ n
  · intro _
    rw [mem_preMasterClo]
    induction n with
    | zero => exact ⟨2, h0⟩
    | succ m ih =>
        rcases ih (Set.mem_univ m) with ⟨k, hk⟩
        exact ⟨k + 1, pre_propagate_succ m k hk⟩

/-- If preChain 1 = ∅, then all preChain n = ∅. -/
theorem preChain1_empty_all_empty
    (h1 : preChain DynPreContext 1 = ∅) :
    ∀ n, preChain DynPreContext n = ∅ := by
  -- Key insight: preChain 1 = ∅ means ∀ p, ¬Halts (DynLR ∅ p)
  -- And preChain (n+1) = { p | Halts (DynLR (preChain n) p) }
  -- If preChain n = ∅, then preChain (n+1) = preChain 1 = ∅
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      cases k with
      | zero => exact h1
      | succ k' =>
          -- Goal: preChain (k'+2) = ∅
          -- ih : preChain (k'+1) = ∅
          rw [show preChain DynPreContext (k' + 1 + 1) =
                   { p | Halts (DynLR (preChain DynPreContext (k' + 1)) p) } by rfl]
          rw [ih]
          -- Now: { p | Halts (DynLR ∅ p) } = ∅, which is h1
          exact h1

/--
**Necessity Theorem**: If MasterClo is univ, then BaseGap is nonempty.
-/
theorem coverage_implies_gap
    (hcover : preMasterClo DynPreContext = Set.univ) :
    ∃ n, n ∈ preBaseGap DynPreContext := by
  -- From coverage, 0 ∈ MasterClo
  have h0 : (0 : ℕ) ∈ preMasterClo DynPreContext := by
    rw [hcover]; exact Set.mem_univ 0
  rcases (mem_preMasterClo DynPreContext 0).1 h0 with ⟨k, hk⟩
  -- Show Chain 1 is nonempty (else coverage fails)
  have hne : (preChain DynPreContext 1).Nonempty := by
    by_contra h1empty
    rw [Set.not_nonempty_iff_eq_empty] at h1empty
    have hall : ∀ n, preChain DynPreContext n = ∅ := preChain1_empty_all_empty h1empty
    -- But hk says 0 ∈ preChain k, contradiction
    rw [hall k] at hk
    exact hk
  -- Pick witness in Chain 1
  rcases hne with ⟨n0, hn0⟩
  -- n0 ∈ BaseGap = Chain 1 \ ProvableSet
  refine ⟨n0, hn0, DynProvable_false n0⟩

/--
**Master Equivalence**: Gap ↔ Coverage (for DynPreContext).
-/
theorem gap_iff_coverage :
    (∃ n, n ∈ preBaseGap DynPreContext) ↔ preMasterClo DynPreContext = Set.univ :=
  ⟨gap_drives_coverage, coverage_implies_gap⟩

-- ============================================================================
-- PART F: Counterexample (no gap → no coverage)
-- ============================================================================

/--
**Counterexample Context**: An LR that never halts at empty context.
-/
def NoGapLR : Set ℕ → ℕ → Trace := fun _ _ _ => False

def NoGapTruth : ℕ → Prop := fun _ => False  -- Nothing is true

/-- The bridge holds vacuously: False ↔ ¬Halts. -/
theorem NoGap_bridge : ∀ n, NoGapTruth n ↔ Halts (NoGapLR ∅ n) := by
  intro n
  constructor
  · intro h; exact False.elim h
  · intro ⟨t, ht⟩; exact ht

def NoGapContext : PreVerifiableContext ℕ where
  Truth := NoGapTruth
  Provable := fun _ => False  -- Nothing provable
  Not := fun n => n
  LR := NoGapLR
  h_bridge := NoGap_bridge

/-- In NoGapContext, Chain 1 = ∅ because LR never halts. -/
theorem NoGap_Chain1_empty : preChain NoGapContext 1 = ∅ := by
  ext n
  simp only [preChain, preNext, preCloK, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨t, ht⟩
  exact ht

/-- In NoGapContext, MasterClo = ∅. -/
theorem NoGap_MasterClo_empty : preMasterClo NoGapContext = ∅ := by
  ext n
  simp only [mem_preMasterClo, Set.mem_empty_iff_false, iff_false]
  intro ⟨k, hk⟩
  induction k with
  | zero => simp [preChain] at hk
  | succ m ih =>
      simp only [preChain, preNext, preCloK, Set.mem_setOf_eq] at hk
      rcases hk with ⟨t, ht⟩
      exact ht

/-- In NoGapContext, BaseGap = ∅ (no gap). -/
theorem NoGap_BaseGap_empty : preBaseGap NoGapContext = ∅ := by
  simp only [preBaseGap, NoGap_Chain1_empty]
  ext n
  simp only [Set.mem_diff, Set.mem_empty_iff_false, false_and]

/-- **Necessity**: Without gap, coverage fails. -/
theorem no_gap_no_coverage :
    ¬ (∃ n, n ∈ preBaseGap NoGapContext) ∧
    preMasterClo NoGapContext ≠ Set.univ := by
  constructor
  · -- No gap
    simp only [NoGap_BaseGap_empty, Set.mem_empty_iff_false, not_exists, not_false_eq_true,
      implies_true]
  · -- MasterClo ≠ univ
    rw [NoGap_MasterClo_empty]
    exact Set.empty_ne_univ

-- ============================================================================
-- PART G: Summary — Gap is STRICTLY the ONLY driver
-- ============================================================================

/-!
**Summary of Gap Indispensability**:

1. `gap_drives_coverage`: If ∃ n ∈ BaseGap, then MasterClo = univ
2. `no_gap_no_coverage`: In NoGapContext, ¬∃ n ∈ BaseGap AND MasterClo ≠ univ

This proves the gap is **indispensable**: coverage requires the gap.
-/

#check gap_drives_coverage   -- Sufficiency: hg → coverage
#check no_gap_no_coverage    -- Necessity: ¬hg ∧ ¬coverage in counterexample

end Instances

end RevHalt
