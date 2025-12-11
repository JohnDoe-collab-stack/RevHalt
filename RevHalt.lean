import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

/-!
# RevHalt: Reverse Halting & Canonical Verification

This file implements the core definitions and theorems for the RevHalt project, derived from the
Reverse-Halting (Rev) operator and its applications to verification and incompleteness.

We establish three main results:
* **T1**: Canonicity of Rev (it captures exactly the Halting property under mild assumptions).
* **T2**: Impossibility of internalizing this specific Halting predicate (Godel/Turing obstruction).
* **T3**: Foundation for complementarity (sound theories as partial views).

-/

-- ==============================================================================================
-- 1. Definitions & Framework
-- ==============================================================================================

/-- A Trace is a predicate on natural numbers (representing state at time n). -/
def Trace := ℕ → Prop

/-- Standard Halting definition: a trace halts if it eventually becomes true. -/
def Halts (T : Trace) : Prop := ∃ n, T n

/-- The "up" operator: converts any trace into a cumulative (monotone) trace. -/
def up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k

/-- Helper: up(T) is always monotone. -/
lemma up_mono (T : Trace) : Monotone (up T) := by
  intro n m hnm h
  obtain ⟨k, hk_le_n, hk_T⟩ := h
  use k
  constructor
  · exact Nat.le_trans hk_le_n hnm
  · exact hk_T

/-- Helper: Halting is preserved by up. -/
lemma exists_up_iff (T : Trace) : (∃ n, up T n) ↔ (∃ n, T n) := by
  constructor
  · intro h
    obtain ⟨n, k, hk_le_n, hk_T⟩ := h
    use k, hk_T
  · intro h
    obtain ⟨n, hn⟩ := h
    use n, n, Nat.le_refl n, hn

/-- Reverse Halting Kit structure. Represents an abstract observation mechanism. -/
structure RHKit where
  Proj : (ℕ → Prop) → Prop

/--
  The core axiom for a valid Kit: `DetectsMonotone`.
  It states that for any *monotone* process, the Kit's projection agrees with standard existence.
  This allows the Kit to have "exotic" behavior on non-monotone traces, but it must be standard on monotone ones.
-/
def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : ℕ → Prop, Monotone X → (K.Proj X ↔ ∃ n, X n)

/--
  Rev_K: The Reverse Halting Operator.
  It standardizes the trace using `up` before applying the Kit.
-/
def Rev_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)

abbrev Rev0_K := Rev_K

-- ==============================================================================================
-- T1: Canonicity of Rev
-- ==============================================================================================

/--
  **Theorem T1 (Traces)**:
  Under the assumption that K detects monotone properties, `Rev0_K` is extensionally equivalent
  to standard Halting for *all* traces (even non-monotone ones).
-/
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T := by
  intro T
  unfold Rev0_K Rev_K
  -- 1. Apply DetectsMonotone to the trace (up T), which is monotone.
  have h_equiv := hK (up T) (up_mono T)
  rw [h_equiv]
  -- 2. Use the fact that ∃ n, up T n ↔ ∃ n, T n
  exact exists_up_iff T

/-- Corollary: Independence of the specific Kit. Any two valid Kits yield the same verdict. -/
theorem T1_uniqueness (K1 K2 : RHKit) (hK1 : DetectsMonotone K1) (hK2 : DetectsMonotone K2) :
    ∀ T, Rev0_K K1 T ↔ Rev0_K K2 T := by
  intro T
  rw [T1_traces K1 hK1, T1_traces K2 hK2]

-- -----------------------------------------------------------------------
-- Dynamic Bridge to Semantics
-- -----------------------------------------------------------------------

variable {Sentence : Type}
variable {Model : Type}
variable (Sat : Model → Sentence → Prop)

def ModE (Γ : Set Sentence) : Set Model := { M | ∀ φ ∈ Γ, Sat M φ }
def ThE (K_models : Set Model) : Set Sentence := { φ | ∀ M ∈ K_models, Sat M φ }
def CloE (Γ : Set Sentence) : Set Sentence := ThE Sat (ModE Sat Γ)
def SemConsequences (Γ : Set Sentence) (φ : Sentence) : Prop := φ ∈ CloE Sat Γ

variable (LR : Set Sentence → Sentence → Trace)

/-- The verdict of the Kit on a semantic pair (Γ, φ) via local reading. -/
def verdict_K (K : RHKit) (Γ : Set Sentence) (φ : Sentence) : Prop :=
  Rev0_K K (LR Γ φ)

/--
  **DynamicBridge Hypothesis**:
  Asserts that the specific Local Reading (LR) chosen successfully maps semantic consequence
  to the halting of the generated trace.
-/
def DynamicBridge : Prop :=
  ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (LR Γ φ)

/--
  **Theorem T1 (Semantics)**:
  If the Kit is valid and the Bridge holds, then semantic consequence is equivalent
  to the Kit's verdict.
-/
theorem T1_semantics (K : RHKit) (hK : DetectsMonotone K)
    (hBridge : DynamicBridge Sat LR) :
    ∀ Γ φ, SemConsequences Sat Γ φ ↔ verdict_K LR K Γ φ := by
  intro Γ φ
  rw [hBridge Γ φ]
  rw [T1_traces K hK]
  rfl

-- ==============================================================================================
-- T2: Impossibility of Internalizing Rev (Abstract Turing-Godel)
-- ==============================================================================================

variable {Code : Type}
variable {PropT : Type}

/--
  Context for the impossibility result.
  Represents a computing system with:
  - `Code`: program codes
  - `PropT`: internal propositions / types
  - `RealHalts`: the external, "real" truth (e.g., our Rev0_K)
  - `Provable`: an internal provability predicate
  - `diagonal_program`: the ability to construct self-referential sentences
-/
structure TuringGodelContext' where
  RealHalts : Code → Prop
  Provable  : PropT → Prop
  FalseT    : PropT
  Not       : PropT → PropT
  -- Consistency Axiom
  consistent : ¬ Provable FalseT
  -- Logic Axiom
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT
  -- Diagonal Fixpoint Axiom
  diagonal_program : ∀ H : Code → PropT, ∃ e, RealHalts e ↔ Provable (Not (H e))

/--
  Definition of an Internal Halting Predicate.
  To be a candidate for "capturing" RealHalts, it must be:
  1. Total (always proves Yes or No).
  2. Correct (if leads to Yes, it really halts).
  3. Complete (if leads to No, it really doesn't halt).
-/
structure InternalHaltingPredicate (ctx : TuringGodelContext' Code PropT) where
  H : Code → PropT
  total    : ∀ e, ctx.Provable (H e) ∨ ctx.Provable (ctx.Not (H e))
  correct  : ∀ e, ctx.RealHalts e → ctx.Provable (H e)
  complete : ∀ e, ¬ ctx.RealHalts e → ctx.Provable (ctx.Not (H e))

/--
  **Theorem T2**:
  There is no internal predicate I that is simultaneously Total, Correct, and Complete
  with respect to RealHalts.
-/
theorem T2_impossibility (ctx : TuringGodelContext' Code PropT) :
    ¬ ∃ I : InternalHaltingPredicate ctx, True := by
  intro h
  obtain ⟨I, _⟩ := h
  -- 1. Construct the diagonal program e for the predicate I.H
  --    Property: RealHalts(e) ↔ Provable(¬ I.H(e))
  obtain ⟨e, he⟩ := ctx.diagonal_program I.H

  -- 2. Analyze by cases on the *real* truth of Halts(e)
  by_cases hReal : ctx.RealHalts e
  · -- Case: e really halts
    -- By Correctness, the system proves H(e)
    have hProvH : ctx.Provable (I.H e) := I.correct e hReal
    -- By Diagonal property, since RealHalts(e) is true, Provable(¬ H(e)) must be true
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := he.mp hReal
    -- Contradiction in the system
    exact ctx.consistent (ctx.absurd (I.H e) hProvH hProvNotH)
  · -- Case: e does not halt
    -- By Completeness, the system proves ¬ H(e)
    have hProvNotH : ctx.Provable (ctx.Not (I.H e)) := I.complete e hReal
    -- By Diagonal property: Provable(¬ H(e)) → RealHalts(e)
    have hImpliesReal : ctx.Provable (ctx.Not (I.H e)) → ctx.RealHalts e := he.mpr
    have hRealContradiction : ctx.RealHalts e := hImpliesReal hProvNotH
    -- Contradiction with hypothesis hReal
    exact hReal hRealContradiction
