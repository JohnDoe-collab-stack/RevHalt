import RevHalt.Theory
import RevHalt.Kinetic
import RevHalt.Oracle
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

end RevHalt
