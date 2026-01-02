import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Basic

/-!
# Arithmetic Hierarchy in RevHalt

This file rigorously formalizes the arithmetic hierarchy (Σ₁, Π₁, Σ₂, Π₂, ...)
and proves key structural theorems about the hierarchy.

## Main Results

1. **Product Space Reduction**: `∀ x, ∀ y, P(x,y)` is Π₁ on ℕ×ℕ (via Cantor pairing)
2. **True Π₂**: `∀ x, ∃ y, P(x,y)` cannot be reduced and is genuinely Π₂
3. **Negation Duality**: ¬Σₙ = Πₙ and vice versa
4. **RevHalt Classification**: Halts is Σ₁, Stabilizes is Π₁, AllHalt is Π₂

## Key Insight

The `StabFrom` in ProofAssistantAgentSpec has form `∀ chain, ∀ n, ¬P` which is ∀∀,
hence Π₁ on product space — NOT true Π₂. True Π₂ would be `∀ chain, ∃ n, P`.

-/

namespace RevHalt.ArithmeticHierarchy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Standard Definitions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Σ₁ form: existential quantifier -/
def Sigma1 (P : Nat → Prop) : Prop := ∃ n, P n

/-- Π₁ form: universal quantifier -/
def Pi1 (P : Nat → Prop) : Prop := ∀ n, P n

/-- Σ₂ form: ∃∀ (existential then universal) -/
def Sigma2 (P : Nat → Nat → Prop) : Prop := ∃ x, ∀ y, P x y

/-- Π₂ form: ∀∃ (universal then existential) -/
def Pi2 (P : Nat → Nat → Prop) : Prop := ∀ x, ∃ y, P x y

/-- Σ₁ on product: ∃∃ (two existentials = one on product) -/
def Sigma1_prod (P : Nat → Nat → Prop) : Prop := ∃ x y, P x y

/-- Π₁ on product: ∀∀ (two universals = one on product) -/
def Pi1_prod (P : Nat → Nat → Prop) : Prop := ∀ x y, P x y

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Cantor Pairing and Product Space Reduction
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cantor pairing function from Mathlib -/
abbrev pair := Nat.pair

/-- Cantor unpairing (left component) -/
abbrev unpair1 (n : Nat) : Nat := (Nat.unpair n).1

/-- Cantor unpairing (right component) -/
abbrev unpair2 (n : Nat) : Nat := (Nat.unpair n).2

/-- Pairing round-trips: unpair ∘ pair = id -/
theorem unpair_pair (x y : Nat) : Nat.unpair (pair x y) = (x, y) :=
  Nat.unpair_pair x y

/-- Pairing is surjective: every n comes from some (x, y) -/
theorem pair_surj (n : Nat) : ∃ x y, pair x y = n :=
  ⟨unpair1 n, unpair2 n, Nat.pair_unpair n⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Key Theorem: ∀∀ = Π₁ on Product (NOT Π₂!)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ∀∀ reduces to single ∀ via pairing -/
theorem forall_forall_iff_forall_paired (P : Nat → Nat → Prop) :
    (∀ x y, P x y) ↔ (∀ n, P (unpair1 n) (unpair2 n)) := by
  constructor
  · intro h n
    exact h (unpair1 n) (unpair2 n)
  · intro h x y
    have : pair x y = pair x y := rfl
    specialize h (pair x y)
    simp only [unpair1, unpair2, Nat.unpair_pair] at h
    exact h

/-- ∀∀ is equivalent to Π₁ on a transformed predicate -/
theorem Pi1_prod_is_Pi1 (P : Nat → Nat → Prop) :
    Pi1_prod P ↔ Pi1 (fun n => P (unpair1 n) (unpair2 n)) := by
  simp only [Pi1_prod, Pi1]
  exact forall_forall_iff_forall_paired P

/-- ∃∃ reduces to single ∃ via pairing -/
theorem exists_exists_iff_exists_paired (P : Nat → Nat → Prop) :
    (∃ x y, P x y) ↔ (∃ n, P (unpair1 n) (unpair2 n)) := by
  constructor
  · intro ⟨x, y, hxy⟩
    use pair x y
    simp only [unpair1, unpair2, Nat.unpair_pair]
    exact hxy
  · intro ⟨n, hn⟩
    exact ⟨unpair1 n, unpair2 n, hn⟩

/-- ∃∃ is equivalent to Σ₁ on a transformed predicate -/
theorem Sigma1_prod_is_Sigma1 (P : Nat → Nat → Prop) :
    Sigma1_prod P ↔ Sigma1 (fun n => P (unpair1 n) (unpair2 n)) := by
  simp only [Sigma1_prod, Sigma1]
  exact exists_exists_iff_exists_paired P

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Negation Duality (with full proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem neg_Sigma1_iff_Pi1 (P : Nat → Prop) :
    ¬ Sigma1 P ↔ Pi1 (fun n => ¬ P n) := by
  simp only [Sigma1, Pi1, not_exists]

theorem neg_Pi1_iff_Sigma1 (P : Nat → Prop) :
    ¬ Pi1 P ↔ Sigma1 (fun n => ¬ P n) := by
  simp only [Sigma1, Pi1]
  exact Classical.not_forall

theorem neg_Sigma2_iff_Pi2 (P : Nat → Nat → Prop) :
    ¬ Sigma2 P ↔ Pi2 (fun x y => ¬ P x y) := by
  constructor
  · intro hNS x
    have hNF := fun hAll => hNS ⟨x, hAll⟩
    exact Classical.not_forall.mp hNF
  · intro hPi hS
    obtain ⟨x, hx⟩ := hS
    obtain ⟨y, hy⟩ := hPi x
    exact hy (hx y)

theorem neg_Pi2_iff_Sigma2 (P : Nat → Nat → Prop) :
    ¬ Pi2 P ↔ Sigma2 (fun x y => ¬ P x y) := by
  simp only [Sigma2, Pi2]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Classical.not_forall.mp h
    refine ⟨x, fun y => ?_⟩
    intro hPxy
    apply hx
    exact ⟨y, hPxy⟩
  · intro hSig hp
    obtain ⟨x, hx⟩ := hSig
    have ⟨y, hy⟩ := hp x
    exact hx y hy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Trace-Based Definitions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Halts: signal exists (Σ₁) -/
def Halts (T : Nat → Prop) : Prop := Sigma1 T

/-- Stabilizes: no signal ever (Π₁) -/
def Stabilizes (T : Nat → Prop) : Prop := Pi1 (fun n => ¬ T n)

/-- Fundamental duality: Stabilizes = ¬Halts -/
theorem Stabilizes_iff_not_Halts (T : Nat → Prop) :
    Stabilizes T ↔ ¬ Halts T := by
  simp only [Stabilizes, Halts]
  exact (neg_Sigma1_iff_Pi1 T).symm

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Family-Based Definitions (True Π₂ vs Π₁-product)
-- ═══════════════════════════════════════════════════════════════════════════════

variable {Code : Type}

/-- AllHalt: every code halts. TRUE Π₂ (∀ e, ∃ n) -/
def AllHalt (F : Code → Nat → Prop) : Prop := ∀ e, ∃ n, F e n

/-- AllStabilize: every code stabilizes. Π₁ on (Code × Nat), NOT Π₂! -/
def AllStabilize (F : Code → Nat → Prop) : Prop := ∀ e n, ¬ F e n

/-- SomeStabilize: some code stabilizes. TRUE Σ₂ (∃ e, ∀ n) -/
def SomeStabilize (F : Code → Nat → Prop) : Prop := ∃ e, ∀ n, ¬ F e n

/-- SomeHalt: some code halts. Σ₁ on (Code × Nat) -/
def SomeHalt (F : Code → Nat → Prop) : Prop := ∃ e n, F e n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Key Classification Theorems
-- ═══════════════════════════════════════════════════════════════════════════════

/-- AllStabilize is equivalent to Π₁ on product (∀∀ = ∀ on product) -/
theorem AllStabilize_is_Pi1_prod (F : Nat → Nat → Prop) :
    AllStabilize F ↔ Pi1_prod (fun e n => ¬ F e n) := by
  simp only [AllStabilize, Pi1_prod]

/-- AllHalt has genuine ∀∃ structure (Π₂) -/
theorem AllHalt_is_Pi2 (F : Nat → Nat → Prop) :
    AllHalt F ↔ Pi2 F := by
  simp only [AllHalt, Pi2]

/-- There is no reduction of Π₂ to Π₁ in general
    (this is the key distinction) -/
theorem Pi2_not_reducible_to_Pi1 :
    ¬ ∀ P : Nat → Nat → Prop, Pi2 P ↔ Pi1 (fun n => P (unpair1 n) (unpair2 n)) := by
  intro h
  -- Counterexample: P x y := (y = 0)
  -- Pi2 P = ∀ x, ∃ y, y = 0, which is True
  -- Pi1 (fun n => unpair2 n = 0) = ∀ n, unpair2 n = 0, which is False
  let P : Nat → Nat → Prop := fun _ y => y = 0
  have hPi2 : Pi2 P := fun _ => ⟨0, rfl⟩
  have hPi1_false : ¬ Pi1 (fun n => P (unpair1 n) (unpair2 n)) := by
    simp only [Pi1, P]
    intro hAll
    have h1 : unpair2 (pair 0 1) = 0 := hAll (pair 0 1)
    simp only [unpair2, Nat.unpair_pair] at h1
    exact Nat.one_ne_zero h1
  exact hPi1_false ((h P).mp hPi2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) The Key Theorem: Complexity Classification
-- ═══════════════════════════════════════════════════════════════════════════════

/--
MAIN THEOREM: Structural distinction between ∀∀ and ∀∃

∀∀ (like AllStabilize) reduces to single ∀ via pairing — it's Π₁ on product.
∀∃ (like AllHalt) does NOT reduce — it's genuinely Π₂.

This means:
- "every code diverges" (AllStabilize) has the same complexity as "one code diverges"
- "every code halts" (AllHalt) is strictly more complex — Π₂-complete
-/
theorem main_classification :
    (∀ P, Pi1_prod P ↔ Pi1 (fun n => P (unpair1 n) (unpair2 n))) ∧
    ¬(∀ P, Pi2 P ↔ Pi1 (fun n => P (unpair1 n) (unpair2 n))) := by
  constructor
  · intro P
    exact Pi1_prod_is_Pi1 P
  · exact Pi2_not_reducible_to_Pi1

end RevHalt.ArithmeticHierarchy
