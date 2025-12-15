import RevHalt.Theory
import RevHalt.Kinetic
import RevHalt.Oracle
import RevHalt.Instances.StratifiedInstance
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Basic

namespace RevHalt

open Set

/-!
# Collatz Extension

Collatz in your framework, A→Z, with:
- inputs indexed by ℕ: n = 1,2,3,...
- the *two local predicates* (even/odd) that drive the step
- LR/Trace dynamics
- Rev verdict indexed by ℕ
- Oracle + Gap specialized to the Collatz-truth instance
-/

-- ======================================================================================
-- 0) Collatz: two predicates + step
-- ======================================================================================

/-- Even predicate (decidable). -/
def EvenP (n : ℕ) : Bool := n % 2 = 0

/-- Collatz step function. -/
def collatz (n : ℕ) : ℕ :=
  if EvenP n then n / 2 else 3*n + 1

-- ======================================================================================
-- 1) Dynamic reading: Trace indexed by ℕ input
-- ======================================================================================

/-- Meta-level Collatz truth: "n reaches 1". -/
def CollatzHits1 (n : ℕ) : Prop :=
  ∃ t : ℕ, collatz^[t] n = 1

/-- Trace carrying the dynamics for input n: true at time t iff iterate t hits 1. -/
def CollatzTrace (n : ℕ) : Trace :=
  fun t => collatz^[t] n = 1

@[simp] theorem Halts_CollatzTrace_iff (n : ℕ) :
    Halts (CollatzTrace n) ↔ CollatzHits1 n := by
  rfl

-- ======================================================================================
-- 1b) Set-equality formulations of Collatz (no ∀)
-- ======================================================================================

/-- Collatz global (set of n that reach 1) = univ -/
def CollatzGlobal : Prop :=
  ({ n : ℕ | CollatzHits1 n } = (univ : Set ℕ))

/-- Equivalent: the set of counterexamples is empty -/
def CollatzNoCounterexample : Prop :=
  ({ n : ℕ | ¬ CollatzHits1 n } = (∅ : Set ℕ))

/-- Equivalence between the two formulations -/
theorem CollatzGlobal_iff_NoCounterexample :
    CollatzGlobal ↔ CollatzNoCounterexample := by
  simp only [CollatzGlobal, CollatzNoCounterexample]
  constructor
  · intro h
    ext n
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
    have : n ∈ ({ m : ℕ | CollatzHits1 m } : Set ℕ) := by rw [h]; exact mem_univ n
    exact this
  · intro h
    ext n
    simp only [mem_setOf_eq, mem_univ, iff_true]
    by_contra hc
    have : n ∈ ({ m : ℕ | ¬ CollatzHits1 m } : Set ℕ) := hc
    rw [h] at this
    exact this

-- ======================================================================================
-- 2) "In your framework": a system instance over PropT = ℕ
-- ======================================================================================

/--
A full Collatz instance over your `GapSystem` (so we have LR + Rev kit + truth bridge).

Inputs are exactly `n : ℕ` (1,2,3,...) and the LR we care about is `LR ∅ n`.
-/
structure CollatzSystem (Code : Type) extends GapSystem Code ℕ where
  /-- Truth on ℕ is Collatz truth (reach 1). -/
  truth_collatz : ∀ n, Truth n ↔ CollatzHits1 n
  /-- The empty-context local reading is the Collatz trace. -/
  lr_collatz    : ∀ n, LR ∅ n = CollatzTrace n

namespace CollatzSystem

variable {Code : Type} (S : CollatzSystem Code)

-- ======================================================================================
-- 3a) Set-equality goals for CollatzSystem
-- ======================================================================================

/-- Goal: the set of Collatz-true inputs equals univ -/
def GoalCollatz : Prop :=
  ({ n : ℕ | CollatzHits1 n } = (univ : Set ℕ))

/-- Goal: the Truth-set equals univ (depends on S) -/
def GoalTruth : Prop :=
  ({ n : ℕ | S.Truth n } = (univ : Set ℕ))

/-- Goal: MasterClo equals univ (depends on S) -/
def CoverGlobal : Prop :=
  (Kinetic.MasterClo S.toVerifiableContext = (univ : Set ℕ))

/-- GoalCollatz ↔ GoalTruth (via truth_collatz) -/
theorem GoalCollatz_iff_GoalTruth :
    GoalCollatz ↔ GoalTruth S := by
  unfold GoalCollatz GoalTruth
  constructor <;> intro h <;> ext n <;> simp only [mem_setOf_eq, mem_univ, iff_true]
  · have : n ∈ ({ m : ℕ | CollatzHits1 m } : Set ℕ) := by rw [h]; exact mem_univ n
    exact (S.truth_collatz n).mpr this
  · have : n ∈ ({ m : ℕ | S.Truth m } : Set ℕ) := by rw [h]; exact mem_univ n
    exact (S.truth_collatz n).mp this

-- ======================================================================================
-- 3b) Rev and Oracle
-- ======================================================================================

/-- The Rev-indexed predicate on ℕ (this is the "input n ↦ verdict" map). -/
def RevPred (n : ℕ) : Prop :=
  Rev0_K S.K (S.LR ∅ n)

/-- The corresponding subset of ℕ recovered by Rev. -/
def RevSet : Set ℕ := { n | S.RevPred n }

@[simp] theorem mem_RevSet_iff (n : ℕ) : n ∈ S.RevSet ↔ S.RevPred n := Iff.rfl

/-- Rev verdict equals Collatz truth (indexed by ℕ). -/
theorem RevPred_iff_Collatz (n : ℕ) :
    S.RevPred n ↔ CollatzHits1 n := by
  unfold RevPred
  -- Rev ↔ Halts (T1)
  have hRev : Rev0_K S.K (S.LR ∅ n) ↔ Halts (S.LR ∅ n) :=
    T1_traces S.K S.hK (S.LR ∅ n)
  -- LR ∅ n = CollatzTrace n
  rw [S.lr_collatz n] at hRev ⊢
  -- Halts (CollatzTrace n) ↔ CollatzHits1 n
  exact hRev.trans (Halts_CollatzTrace_iff n)

/-- Set-level identification: Rev recovers exactly the Collatz-true inputs (as a subset of ℕ). -/
theorem RevSet_eq_CollatzTrue :
    S.RevSet = { n : ℕ | CollatzHits1 n } := by
  ext n
  simp only [RevSet, mem_setOf_eq, S.RevPred_iff_Collatz]

/-- Complement (full information on ℕ): Rev-negative inputs are exactly the Collatz-false inputs. -/
theorem RevSet_compl_eq_CollatzFalse :
    (S.RevSet)ᶜ = { n : ℕ | ¬ CollatzHits1 n } := by
  ext n
  simp only [mem_compl_iff, RevSet, mem_setOf_eq, S.RevPred_iff_Collatz]

-- ======================================================================================
-- 3) Oracle + Gap (using your Oracle file, not ad hoc)
-- ======================================================================================

/-- The canonical Rev-oracle on PropT = ℕ (built from LR + kit). -/
def Oracle : TruthOracle S.toEnrichedContext :=
{ O := fun n => Rev0_K S.K (S.LR ∅ n)
  O_correct := by
    intro n
    have hRev : Rev0_K S.K (S.LR ∅ n) ↔ Halts (S.LR ∅ n) :=
      T1_traces S.K S.hK (S.LR ∅ n)
    have hBr : S.Truth n ↔ Halts (S.LR ∅ n) := S.h_bridge n
    exact hRev.trans hBr.symm }

/-- Oracle verdict is Collatz truth (indexed by ℕ). -/
theorem Oracle_iff_Collatz (n : ℕ) :
    (S.Oracle.O n) ↔ CollatzHits1 n := by
  -- Oracle.O n ↔ Truth n ↔ CollatzHits1 n
  have hT : S.Oracle.O n ↔ S.Truth n := S.Oracle.O_correct n
  exact hT.trans (S.truth_collatz n)

/--
Gap specialized to Collatz: there exists an input n such that Collatz is true
but unprovable in the internal `Provable` (needs soundness, exactly as your Oracle API).
-/
theorem Collatz_gap_witness
    (h_sound : ∀ p : ℕ, S.Provable p → S.Truth p) :
    ∃ n : ℕ, CollatzHits1 n ∧ ¬ S.Provable n := by
  -- Apply your "oracle authority = gap + strictness" to S and its Oracle
  have h :=
    oracle_authority_is_gap
      (ctx := S.toVerifiableContext)
      (oracle := S.Oracle)
      (h_sound := h_sound)
  rcases h.2.2 with ⟨n, hOn, hNP⟩
  have hC : CollatzHits1 n := (S.Oracle_iff_Collatz n).1 hOn
  exact ⟨n, hC, hNP⟩

end CollatzSystem

-- ======================================================================================
-- 4) Conditional Collatz via Gap-Cover (But A)
-- ======================================================================================

/--
**Collatz follows from ContextSound + LRPropagatesFromGap**.

This is the conditional formulation: we do NOT prove these hypotheses,
but we show that IF they hold for a CollatzSystem, THEN Collatz is true.

Proof structure:
1. Gap exists (from T2)
2. LRPropagatesFromGap: g ∈ BaseGap → ∀ p, Halts (LR {g} p)
3. ContextSound + Truth g → ∀ p, Truth p
4. truth_collatz: Truth p ↔ CollatzHits1 p
5. Therefore: ∀ n, CollatzHits1 n
-/
theorem Collatz_from_propagation
    {Code : Type}
    (S : CollatzSystem Code)
    (hCS : Kinetic.ContextSound S.toVerifiableContext)
    (hProp : Kinetic.LRPropagatesFromGap S.toVerifiableContext) :
    ∀ n : ℕ, CollatzHits1 n := by
  -- Step 1: Gap exists (from T2)
  have hGap : ∃ g, g ∈ Kinetic.BaseGap S.toVerifiableContext :=
    Kinetic.gap_always_exists S.toVerifiableContext
  -- Step 2: Apply gap_drives_cover (needs to import StratifiedInstance theorems)
  -- For now, inline the logic:
  obtain ⟨g, hg⟩ := hGap
  -- g is true (BaseGap ⊆ TruthSet)
  have hgTrue : S.Truth g :=
    (Kinetic.mem_BaseGap_iff_truth_not_provable S.toVerifiableContext g).mp hg |>.1
  -- From LRPropagatesFromGap: ∀ p, Halts (LR {g} p)
  have hAllHalt : ∀ p, Halts (S.LR ({g} : Set ℕ) p) := hProp g hg
  -- Under ContextSound: ∀ p, Truth p
  have hAllTrue : ∀ p, S.Truth p := fun p => by
    apply hCS ({g} : Set ℕ) p
    · intro ψ hψ
      have : ψ = g := hψ
      rw [this]; exact hgTrue
    · exact hAllHalt p
  -- Via truth_collatz: ∀ n, CollatzHits1 n
  intro n
  exact (S.truth_collatz n).mp (hAllTrue n)

end RevHalt
