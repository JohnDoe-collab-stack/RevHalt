import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic

/-!
# StructuralDichotomy

The abstract schema that RevHalt instantiates.

## Core Insight

A dichotomy D₁/D₂ is **structural** (not merely extensional) when:
1. There exists an operator O with a universal property
2. The kernel of O characterizes one side: `O x = ⊥ ↔ ¬Sig x`
3. The signal is preserved: `Sig (O x) ↔ Sig x`

## Separation of Principles

- **EM** is needed exactly at `¬¬Sig x → Sig x` (deciding the side)
- **AC** is NOT needed (the "choice" is forced by the structure)
- **Computability** is blocked by T2 (uniform decision is impossible)

## Instantiation

RevHalt instantiates this schema with:
- X = Trace
- O = up
- Sig = Halts
- ker_iff = up_eq_bot_iff
- sig_invar = exists_up_iff
-/

namespace RevHalt

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) The Abstract Schema
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A **structural dichotomy**: an operator O with ⊥, a predicate Sig ("signal"),
signal invariance, and kernel identification with ¬Sig.

This is the abstract interface that captures when a dichotomy is "geometric"
rather than merely "extensional".
-/
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  /-- The structural operator (projector/coreflector) -/
  O : X → X
  /-- O is monotone -/
  mono : Monotone O
  /-- O is idempotent -/
  idem : ∀ x, O (O x) = O x
  /-- The "signal" predicate (Σ₁-like: existence of witness) -/
  Sig : X → Prop
  /-- O preserves the signal -/
  sig_invar : ∀ x, Sig (O x) ↔ Sig x
  /-- Kernel = ¬Signal (Π₁-like: absence of witness) -/
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x

namespace StructuralDichotomy

variable {X : Type} [Preorder X] [Bot X] (D : StructuralDichotomy X)

-- ───────────────────────────────────────────────────────────────────────────────
-- Constructive theorems (no classical logic needed)
-- ───────────────────────────────────────────────────────────────────────────────

/-- Constructive: Signal implies not-in-kernel -/
theorem sig_imp_ne_bot (x : X) : D.Sig x → D.O x ≠ ⊥ := by
  intro hs hO
  have hns : ¬ D.Sig x := (D.ker_iff x).1 hO
  exact hns hs

/-- Constructive: Not-in-kernel implies double-negation of signal -/
theorem ne_bot_imp_notnot_sig (x : X) : D.O x ≠ ⊥ → ¬¬ D.Sig x := by
  intro hne hns
  have : D.O x = ⊥ := (D.ker_iff x).2 hns
  exact hne this

/-- Constructive: In kernel implies no signal -/
theorem bot_imp_not_sig (x : X) : D.O x = ⊥ → ¬ D.Sig x := by
  intro hbot
  exact (D.ker_iff x).1 hbot

/-- Constructive: No signal implies in kernel -/
theorem not_sig_imp_bot (x : X) : ¬ D.Sig x → D.O x = ⊥ := by
  intro hns
  exact (D.ker_iff x).2 hns

-- ───────────────────────────────────────────────────────────────────────────────
-- Classical theorem (EM enters HERE and ONLY here)
-- ───────────────────────────────────────────────────────────────────────────────

/-- Classical: Not-in-kernel implies signal. THIS is where EM is needed. -/
theorem ne_bot_imp_sig (x : X) : D.O x ≠ ⊥ → D.Sig x := by
  classical
  intro hne
  have : ¬¬ D.Sig x := D.ne_bot_imp_notnot_sig x hne
  exact Classical.not_not.mp this

/-- The full equivalence (classical) -/
theorem sig_iff_ne_bot (x : X) : D.Sig x ↔ D.O x ≠ ⊥ :=
  ⟨D.sig_imp_ne_bot x, D.ne_bot_imp_sig x⟩

-- ───────────────────────────────────────────────────────────────────────────────
-- Derived structure
-- ───────────────────────────────────────────────────────────────────────────────

/-- The kernel of O -/
def Ker : Set X := { x | D.O x = ⊥ }

/-- Kernel membership iff no signal -/
theorem mem_Ker_iff (x : X) : x ∈ D.Ker ↔ ¬ D.Sig x := D.ker_iff x

/-- The "image" (fixed points of O) -/
def Fix : Set X := { x | D.O x = x }

/-- O x is always a fixed point -/
theorem O_mem_Fix (x : X) : D.O x ∈ D.Fix := by
  unfold Fix
  simp only [Set.mem_setOf_eq]
  exact D.idem x

/-- The dichotomy: every x is either in Ker or has signal (classical) -/
theorem dichotomy (x : X) : x ∈ D.Ker ∨ D.Sig x := by
  classical
  by_cases h : D.Sig x
  · exact Or.inr h
  · exact Or.inl ((D.ker_iff x).2 h)

/-- The dichotomy is exclusive -/
theorem dichotomy_exclusive (x : X) : ¬ (x ∈ D.Ker ∧ D.Sig x) := by
  intro ⟨hker, hsig⟩
  have hns := D.bot_imp_not_sig x hker
  exact hns hsig

end StructuralDichotomy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Abstract Dynamics (derived from the schema)
-- ═══════════════════════════════════════════════════════════════════════════════

section AbstractDynamics

variable {X : Type} [Preorder X] [Bot X] (D : StructuralDichotomy X)

/--
A Pick for a structural dichotomy:
- `side` indicates which side (true = signal, false = kernel)
- `cert` is the proof of the side
-/
structure SDPick (x : X) where
  side : Bool
  cert : if side then D.Sig x else D.O x = ⊥

/-- Truth of a pick: the underlying proposition is true -/
def SDPick.truth {x : X} (pick : SDPick D x) : Prop :=
  if pick.side then D.Sig x else ¬ D.Sig x

/-- Every pick is true (by construction) -/
theorem SDPick.is_true {x : X} (pick : SDPick D x) : pick.truth D := by
  unfold SDPick.truth
  split
  next hTrue =>
    have hcert : D.Sig x := by
      have p_eq : pick.side = true := hTrue
      have c := pick.cert
      rw [p_eq] at c
      simp only [↓reduceIte] at c
      exact c
    exact hcert
  next hFalse =>
    have hcert : D.O x = ⊥ := by
      have p_eq : pick.side = false := Bool.eq_false_iff.mpr hFalse
      have c := pick.cert
      rw [p_eq] at c
      exact c
    exact D.bot_imp_not_sig x hcert


/-- A pick oracle for a structural dichotomy: for every element, a pick -/
def SDOracle (Index : Type) (elem : Index → X) : Type :=
  ∀ i : Index, SDPick D (elem i)

end AbstractDynamics

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Instantiation: Trace/up
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Trace type -/
def Trace := ℕ → Prop

/-- Bottom trace -/
def botTrace : Trace := fun _ => False

instance : Bot Trace := ⟨botTrace⟩

/-- Pointwise order on traces -/
instance : Preorder Trace where
  le := fun T U => ∀ n, T n → U n
  le_refl := fun _ _ h => h
  le_trans := fun _ _ _ hab hbc n h => hbc n (hab n h)

/-- The up operator -/
def up (T : Trace) : Trace := fun n => ∃ k, k ≤ n ∧ T k

/-- Halts predicate -/
def Halts (T : Trace) : Prop := ∃ n, T n

/-- up is monotone -/
theorem up_mono : Monotone up := by
  intro T U h n ⟨k, hkn, hTk⟩
  exact ⟨k, hkn, h k hTk⟩

/-- up is idempotent -/
theorem up_idem (T : Trace) : up (up T) = up T := by
  funext n
  apply propext
  constructor
  · intro ⟨k, hkn, j, hjk, hTj⟩
    exact ⟨j, Nat.le_trans hjk hkn, hTj⟩
  · intro ⟨k, hkn, hTk⟩
    exact ⟨k, hkn, k, Nat.le_refl k, hTk⟩

/-- Signal invariance: Halts (up T) ↔ Halts T -/
theorem exists_up_iff (T : Trace) : Halts (up T) ↔ Halts T := by
  constructor
  · intro ⟨n, k, _, hTk⟩
    exact ⟨k, hTk⟩
  · intro ⟨n, hn⟩
    exact ⟨n, n, Nat.le_refl n, hn⟩

/-- Kernel characterization: up T = ⊥ ↔ ¬ Halts T -/
theorem up_eq_bot_iff (T : Trace) : up T = ⊥ ↔ ¬ Halts T := by
  constructor
  · intro h ⟨n, hn⟩
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    have hbot : up T = ⊥ := h
    rw [hbot] at this
    exact this
  · intro h
    funext n
    apply propext
    constructor
    · intro ⟨k, _, hTk⟩
      exact h ⟨k, hTk⟩
    · intro hbot
      exact False.elim hbot

/--
**THE INSTANTIATION**: Trace/up is a StructuralDichotomy.

This single definition captures all of RevHalt's structure.
-/
def traceSD : StructuralDichotomy Trace where
  O := up
  mono := up_mono
  idem := up_idem
  Sig := Halts
  sig_invar := exists_up_iff
  ker_iff := up_eq_bot_iff

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Verification: the abstract theorems specialize correctly
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Stabilizes = in kernel of up -/
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

/-- Stabilizes ↔ ¬Halts -/
theorem Stabilizes_iff_not_Halts (T : Trace) : Stabilizes T ↔ ¬ Halts T := by
  constructor
  · intro hs ⟨n, hn⟩
    exact hs n hn
  · intro hnh n hn
    exact hnh ⟨n, hn⟩

/-- Kernel of traceSD = Stabilizes -/
theorem traceSD_ker_eq_stabilizes (T : Trace) :
    T ∈ traceSD.Ker ↔ Stabilizes T := by
  rw [StructuralDichotomy.mem_Ker_iff]
  unfold traceSD
  simp only
  rw [Stabilizes_iff_not_Halts]

/-- The abstract sig_iff_ne_bot specializes to: Halts T ↔ up T ≠ ⊥ -/
example (T : Trace) : Halts T ↔ up T ≠ ⊥ :=
  traceSD.sig_iff_ne_bot T

/-- The abstract dichotomy specializes to: Stabilizes T ∨ Halts T -/
example (T : Trace) : T ∈ traceSD.Ker ∨ Halts T :=
  traceSD.dichotomy T

end RevHalt
