import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic



/-!
# Ordinal Boundary Theorem - Mechanical Verification

## Thesis: Two Distinct Sources of Classical Logic

The analysis reveals two distinct sources of non-constructive behavior:

1. **Trace Class (Prop)**: Quantifying over arbitrary traces `ℕ → Prop` yields **EM** immediately, even at stage 0.
2. **Ordinal (ω)**: Passing from finite checking to the limit $\omega$ on *decidable* traces yields **LPO**.

Note: They are distinct in origin (class vs ordinal), though in logical strength EM implies LPO.

The combination (Limit + Arbitrary) is equivalent to EM, but `stage_zero_is_em` proves that the arbitrary quantification alone is sufficient for EM.
-/
namespace RevHalt.OrdinalMechanical

-- ═══════════════════════════════════════════════════════════════════════════════
-- 0) LPO FORMALIZATION (THE ORDINAL GAP)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- LPO in Bool: standard form -/
def LPOBool : Prop :=
  ∀ f : ℕ → Bool, (∃ n, f n = true) ∨ (∀ n, f n = false)

/-- LPO in Prop: decidable predicates -/
def LPOProp : Prop :=
  ∀ p : ℕ → Prop, (∀ n, Decidable (p n)) → (∃ n, p n) ∨ (∀ n, ¬ p n)

/-- The Ordinal Gap on decidable traces is exactly LPO -/
theorem LPOBool_iff_LPOProp : LPOBool ↔ LPOProp := by
  constructor
  · intro h p hp
    let f : ℕ → Bool := fun n => @decide (p n) (hp n)
    cases h f with
    | inl hT =>
      left
      rcases hT with ⟨n, hn⟩
      exists n
      exact of_decide_eq_true hn
    | inr hF =>
      right
      intro n
      have := hF n
      exact of_decide_eq_false this
  · intro h f
    cases h (fun n => f n = true) (fun n => inferInstance) with
    | inl hT => left; exact hT
    | inr hF => right; intro n; exact Bool.eq_false_iff.mpr (hF n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) BASIC DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Trace: arbitrary predicate on ℕ -/
def Trace := ℕ → Prop

/-- Halts: Σ₁ -/
def Halts (T : Trace) : Prop := ∃ n, T n

/-- Stabilizes: Π₁ -/
def Stabilizes (T : Trace) : Prop := ∀ n, ¬ T n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) FINITE APPROXIMATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HaltsUpTo m: there exists a witness ≤ m -/
def HaltsUpTo (T : Trace) (m : ℕ) : Prop := ∃ n, n ≤ m ∧ T n

/-- StabilizesUpTo m: no witness ≤ m -/
def StabilizesUpTo (T : Trace) (m : ℕ) : Prop := ∀ n, n ≤ m → ¬ T n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) FINITE STAGES ARE DECIDABLE (for decidable traces)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HaltsUpTo is decidable for decidable traces -/
def halts_up_to_decidable (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    Decidable (HaltsUpTo T m) := by
  induction m with
  | zero =>
    by_cases h : T 0
    · exact isTrue ⟨0, Nat.le_refl 0, h⟩
    · exact isFalse (fun ⟨n, hn, hTn⟩ => by
        have : n = 0 := Nat.le_zero.mp hn
        rw [this] at hTn
        exact h hTn)
  | succ k ih =>
    cases ih with
    | isTrue ht =>
      exact isTrue (ht.elim fun n ⟨hn, hTn⟩ => ⟨n, Nat.le_succ_of_le hn, hTn⟩)
    | isFalse hf =>
      by_cases hk : T (k + 1)
      · exact isTrue ⟨k + 1, Nat.le_refl _, hk⟩
      · exact isFalse (fun ⟨n, hn, hTn⟩ => by
          cases Nat.lt_or_eq_of_le hn with
          | inl hlt => exact hf ⟨n, Nat.lt_succ_iff.mp hlt, hTn⟩
          | inr heq => rw [heq] at hTn; exact hk hTn)

/-- StabilizesUpTo is decidable for decidable traces -/
def stabilizes_up_to_decidable (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    Decidable (StabilizesUpTo T m) := by
  induction m with
  | zero =>
    by_cases h : T 0
    · exact isFalse (fun hs => hs 0 (Nat.le_refl 0) h)
    · exact isTrue (fun n hn => by have : n = 0 := Nat.le_zero.mp hn; rw [this]; exact h)
  | succ k ih =>
    cases ih with
    | isFalse hf =>
      exact isFalse (fun hs => hf (fun n hn => hs n (Nat.le_succ_of_le hn)))
    | isTrue ht =>
      by_cases hk : T (k + 1)
      · exact isFalse (fun hs => hs (k + 1) (Nat.le_refl _) hk)
      · exact isTrue (fun n hn => by
          cases Nat.lt_or_eq_of_le hn with
          | inl hlt => exact ht n (Nat.lt_succ_iff.mp hlt)
          | inr heq => rw [heq]; exact hk)

/-- The dichotomy at stage m is decidable -/
def dichotomy_up_to_decidable (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    Decidable (HaltsUpTo T m ∨ StabilizesUpTo T m) := by
  cases halts_up_to_decidable T m with
  | isTrue h => exact isTrue (Or.inl h)
  | isFalse hf =>
    cases stabilizes_up_to_decidable T m with
    | isTrue hs => exact isTrue (Or.inr hs)
    | isFalse hsf => exact isFalse (fun h => h.elim hf hsf)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) FINITE DICHOTOMY ALWAYS HOLDS (constructively!)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- At each finite stage, the dichotomy holds constructively for decidable traces -/
theorem dichotomy_up_to (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    HaltsUpTo T m ∨ StabilizesUpTo T m := by
  cases dichotomy_up_to_decidable T m with
  | isTrue h => exact h
  | isFalse hf =>
    -- This case is actually impossible, but we prove it anyway
    right
    intro n hn hTn
    apply hf
    left
    exact ⟨n, hn, hTn⟩

/--
Direct proof by induction (still requires decidability of T).

Note: For *arbitrary* traces (ℕ → Prop), even the finite stage dichotomy
would require deciding `T n`, which is EM for specific propositions.
So "Constructive at finite stages" implicitly assumes we are working with
computable/decidable data (Bits), not arbitrary propositions.
-/
theorem dichotomy_up_to_direct (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    HaltsUpTo T m ∨ StabilizesUpTo T m := by
  induction m with
  | zero =>
    by_cases h : T 0
    · exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    · exact Or.inr (fun n hn => by have : n = 0 := Nat.le_zero.mp hn; rw [this]; exact h)
  | succ k ih =>
    cases ih with
    | inl hH =>
      left
      exact hH.elim fun n ⟨hn, hTn⟩ => ⟨n, Nat.le_succ_of_le hn, hTn⟩
    | inr hS =>
      by_cases hk : T (k + 1)
      · left; exact ⟨k + 1, Nat.le_refl _, hk⟩
      · right
        intro n hn
        cases Nat.lt_or_eq_of_le hn with
        | inl hlt => exact hS n (Nat.lt_succ_iff.mp hlt)
        | inr heq => rw [heq]; exact hk

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) CONNECTION BETWEEN FINITE AND LIMIT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Halts ↔ ∃m, HaltsUpTo m -/
theorem halts_iff_exists_halts_up_to (T : Trace) :
    Halts T ↔ ∃ m, HaltsUpTo T m := by
  constructor
  · intro ⟨n, hn⟩
    exact ⟨n, n, Nat.le_refl n, hn⟩
  · intro ⟨m, n, _, hn⟩
    exact ⟨n, hn⟩

/-- Stabilizes ↔ ∀m, StabilizesUpTo m -/
theorem stabilizes_iff_forall_stabilizes_up_to (T : Trace) :
    Stabilizes T ↔ ∀ m, StabilizesUpTo T m := by
  constructor
  · intro hs m n _ hTn
    exact hs n hTn
  · intro hall n hn
    exact hall n n (Nat.le_refl n) hn

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) THE ORDINAL GAP: FINITE STAGES DON'T GIVE LIMIT
-- ═══════════════════════════════════════════════════════════════════════════════

-- Key insight: Having the dichotomy at ALL finite stages does NOT give the limit dichotomy.
-- For decidable traces, we have ∀m, (HaltsUpTo T m ∨ StabilizesUpTo T m).
-- But this does NOT imply Halts T ∨ Stabilizes T without EM.

/-- All finite stages hold (for decidable traces) -/
theorem all_finite_stages (T : Trace) [∀ n, Decidable (T n)] :
    ∀ m, HaltsUpTo T m ∨ StabilizesUpTo T m :=
  dichotomy_up_to T

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) THE EM EQUIVALENCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Constant trace encoding -/
def constTrace (P : Prop) : Trace := fun _ => P

/-- Halts for constant trace ↔ P -/
theorem Halts_constTrace_iff (P : Prop) : Halts (constTrace P) ↔ P := by
  constructor
  · intro ⟨_, hn⟩; exact hn
  · intro h; exact ⟨0, h⟩

/-- Stabilizes for constant trace ↔ ¬P -/
theorem Stabilizes_constTrace_iff (P : Prop) : Stabilizes (constTrace P) ↔ ¬P := by
  constructor
  · intro hs hP; exact hs 0 hP
  · intro hP n hn; exact hP hn

/-- Constructive: Stabilizes ↔ ¬Halts -/
theorem stabilizes_iff_not_halts (T : Trace) : Stabilizes T ↔ ¬ Halts T := by
  constructor
  · intro hs ⟨n, hn⟩; exact hs n hn
  · intro hnh n hn; exact hnh ⟨n, hn⟩

/-- EM → Dichotomy (no axioms) -/
theorem dichotomy_from_em (em : ∀ P : Prop, P ∨ ¬P) (T : Trace) :
    Halts T ∨ Stabilizes T :=
  (em (Halts T)).elim Or.inl (fun h => Or.inr ((stabilizes_iff_not_halts T).mpr h))

/-- Dichotomy → EM (no axioms) -/
theorem em_from_dichotomy (dich : ∀ T : Trace, Halts T ∨ Stabilizes T) :
    ∀ P : Prop, P ∨ ¬P := by
  intro P
  cases dich (constTrace P) with
  | inl hH => exact Or.inl ((Halts_constTrace_iff P).mp hH)
  | inr hS => exact Or.inr ((Stabilizes_constTrace_iff P).mp hS)

/-- THE EQUIVALENCE: Dichotomy ↔ EM -/
theorem dichotomy_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬P) :=
  ⟨em_from_dichotomy, fun em T => dichotomy_from_em em T⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) THE ORDINAL CHARACTERIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## The Ordinal Structure - Mechanically Verified

### Stage n < ω (finite)
- `HaltsUpTo T n` : decidable (for **decidable** T)
- `StabilizesUpTo T n` : decidable (for **decidable** T)
- `HaltsUpTo T n ∨ StabilizesUpTo T n` : **Always true** (for decidable T)

### Stage ω (limit)
- `Halts T ∨ Stabilizes T` : **Equivalent to EM** (for **arbitrary** T)

### The Double Gap
The boundary involves TWO jumps:
1. **Ordinal**: Finite stage `n` → Limit `ω`
2. **Class**: Decidable traces (`ℕ → Bool`) → Arbitrary traces (`ℕ → Prop`)

If we restricted the limit to decidable traces, we would get **LPO** (a weaker principle than EM).
If we allowed arbitrary traces at finite stages, we would need EM immediately (see below).

The equivalence `Dichotomy ↔ EM` relies on quantifying over **arbitrary** traces `ℕ → Prop`.
-/

/-- Summary: finite stage dichotomy requires no EM -/
theorem finite_stage_no_em (T : Trace) [∀ n, Decidable (T n)] (m : ℕ) :
    HaltsUpTo T m ∨ StabilizesUpTo T m :=
  dichotomy_up_to T m

/-- Summary: limit dichotomy IS EM -/
theorem limit_stage_is_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬ P) :=
  dichotomy_iff_em


/-- Stage 0 for arbitrary traces is already EM -/
theorem stage_zero_is_em :
    (∀ T : Trace, HaltsUpTo T 0 ∨ StabilizesUpTo T 0) ↔ (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · intro h P
    cases h (constTrace P) with
    | inl hH =>
      let ⟨_, _, hP⟩ := hH
      exact Or.inl hP
    | inr hS =>
      exact Or.inr (hS 0 (Nat.le_refl 0))
  · intro em T
    cases em (T 0) with
    | inl hT => left; exact ⟨0, Nat.le_refl 0, hT⟩
    | inr hnT => right; intro n hn; rw [Nat.le_zero.mp hn]; exact hnT

-- ═══════════════════════════════════════════════════════════════════════════════
-- 10) VERIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

-- Finite stages: no axioms
#print axioms LPOBool_iff_LPOProp
#print axioms halts_up_to_decidable
#print axioms stabilizes_up_to_decidable
#print axioms dichotomy_up_to_decidable
#print axioms dichotomy_up_to
#print axioms dichotomy_up_to_direct
#print axioms all_finite_stages

-- Connection lemmas: no axioms
#print axioms halts_iff_exists_halts_up_to
#print axioms stabilizes_iff_forall_stabilizes_up_to

-- EM equivalence: no axioms
#print axioms dichotomy_from_em
#print axioms em_from_dichotomy
#print axioms dichotomy_iff_em

-- Summary theorems: no axioms
#print axioms finite_stage_no_em
#print axioms limit_stage_is_em

-- Stage 0 analysis: no axioms
#print axioms stage_zero_is_em

end RevHalt.OrdinalMechanical
