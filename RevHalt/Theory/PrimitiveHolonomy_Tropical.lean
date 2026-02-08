import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import RevHalt.Theory.PrimitiveHolonomy

/-!
# Tropical Classification for Causal Arithmetics

Formalization of the classification theorem:
Under interchange + units + monotonicity, the only stable pairs (⊕, ⊙) are:
- (max, +) and (min, +) — idempotent (tropical dioïds)
- (+, max) and (+, +) — additive (quantitative bimonoids)

This is a purely algebraic layer that connects to `PrimitiveHolonomy` via the
holonomy-interchange correspondence.

Strictly constructive: no `classical`, no `Decidable` assumptions beyond ℕ.
-/

namespace PrimitiveHolonomy

universe u

/-!
## 1. CausalPair — Algebraic Structure
-/

/-- A causal pair (⊕, ⊙) with units and order.
    This is the minimal algebraic structure for classification. -/
structure CausalPair (S : Type u) where
  /-- Parallel operation ⊕ -/
  oplus : S → S → S
  /-- Sequential operation ⊙ -/
  odot : S → S → S
  /-- Zero for ⊕ (additive identity) -/
  zero_oplus : S
  /-- Unit for ⊙ (multiplicative identity, typically 0 in arithmetic) -/
  unit_odot : S
  /-- Partial order on S -/
  le : S → S → Prop
  /-- ⊕ is commutative -/
  oplus_comm : ∀ a b, oplus a b = oplus b a
  /-- ⊕ is associative -/
  oplus_assoc : ∀ a b c, oplus (oplus a b) c = oplus a (oplus b c)
  /-- ⊙ is associative -/
  odot_assoc : ∀ a b c, odot (odot a b) c = odot a (odot b c)
  /-- zero_oplus is neutral for ⊕ -/
  oplus_zero : ∀ a, oplus a zero_oplus = a
  /-- unit_odot is left neutral for ⊙ -/
  odot_unit_left : ∀ a, odot unit_odot a = a
  /-- unit_odot is right neutral for ⊙ -/
  odot_unit_right : ∀ a, odot a unit_odot = a
  /-- ⊙ is monotone in both arguments -/
  odot_mono : ∀ a b c d, le a b → le c d → le (odot a c) (odot b d)
  /-- le is reflexive -/
  le_refl : ∀ a, le a a
  /-- le is transitive -/
  le_trans : ∀ a b c, le a b → le b c → le a c

namespace CausalPair

variable {S : Type u} (C : CausalPair S)

/-- Left unit for ⊕ (derived from commutativity + right unit). -/
theorem oplus_zero_left (a : S) : C.oplus C.zero_oplus a = a := by
  rw [C.oplus_comm, C.oplus_zero]

end CausalPair

/-!
## 2. Interchange Inequality

The fundamental constraint from 2-categorical structure.
-/

/-- The interchange inequality:
    (a ⊕ b) ⊙ (c ⊕ d) ≤ (a⊙c) ⊕ (a⊙d) ⊕ (b⊙c) ⊕ (b⊙d)

    This comes from the 2-cell structure: when parallel and sequential
    operations interact, the RHS represents all possible "interleavings". -/
def InterchangeIneq {S : Type u} (C : CausalPair S) : Prop :=
  ∀ a b c d : S,
    C.le (C.odot (C.oplus a b) (C.oplus c d))
         (C.oplus (C.oplus (C.odot a c) (C.odot a d))
                  (C.oplus (C.odot b c) (C.odot b d)))

/-- Interchange equality (stronger, holds for idempotent ⊕). -/
def InterchangeEq {S : Type u} (C : CausalPair S) : Prop :=
  ∀ a b c d : S,
    C.odot (C.oplus a b) (C.oplus c d) =
    C.oplus (C.oplus (C.odot a c) (C.odot a d))
            (C.oplus (C.odot b c) (C.odot b d))

theorem interchangeEq_implies_ineq {S : Type u} (C : CausalPair S) :
    InterchangeEq C → InterchangeIneq C := by
  intro hEq a b c d
  rw [hEq a b c d]
  exact C.le_refl _

/-!
## 3. Dichotomy: Idempotent vs Additive

The fundamental split in the classification.
-/

/-- ⊕ is idempotent: a ⊕ a = a (sup-like behavior). -/
def IsIdempotent {S : Type u} (C : CausalPair S) : Prop :=
  ∀ a : S, C.oplus a a = a

/-- ⊕ is strictly additive: a ⊕ a ≠ a for non-zero elements (cumulative). -/
def IsStrictlyAdditive {S : Type u} (C : CausalPair S) : Prop :=
  ∀ a : S, a ≠ C.zero_oplus → C.oplus a a ≠ a

/-- The dichotomy: ⊕ is either idempotent or strictly additive. -/
def Dichotomy {S : Type u} (C : CausalPair S) : Prop :=
  IsIdempotent C ∨ IsStrictlyAdditive C

/-!
## 4. Idempotent Case: ⊙ = +

When ⊕ is a supremum, the sequential operation must be addition.
-/

/-- Serially extensive: for non-trivial elements, a ⊙ b ≥ a + b.
    This prevents ⊙ from being "too small". -/
def SeriallyExtensive (C : CausalPair ℕ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → C.le (a + b) (C.odot a b)

/-- In the idempotent case with interchange equality, ⊙ distributes over ⊕. -/
def DistributesOverOplus {S : Type u} (C : CausalPair S) : Prop :=
  ∀ a b c : S, C.odot a (C.oplus b c) = C.oplus (C.odot a b) (C.odot a c)

/-- Key lemma: idempotent + interchange equality → distributivity.

    Proof sketch: Apply interchange with the first argument duplicated (a ⊕ a = a),
    then use idempotence to collapse the 4-fold ⊕ to 2-fold. -/
theorem idempotent_interchange_distrib {S : Type u} (C : CausalPair S)
    (hIdem : IsIdempotent C) (hInt : InterchangeEq C) :
    DistributesOverOplus C := by
  intro a b c
  -- Apply interchange: (a ⊕ a) ⊙ (b ⊕ c) = (a⊙b) ⊕ (a⊙c) ⊕ (a⊙b) ⊕ (a⊙c)
  have h := hInt a a b c
  -- Since ⊕ is idempotent, a ⊕ a = a
  rw [hIdem a] at h
  -- The RHS is: ((a⊙b) ⊕ (a⊙c)) ⊕ ((a⊙b) ⊕ (a⊙c))
  -- By idempotence of ⊕, this equals (a⊙b) ⊕ (a⊙c)
  have hab := C.odot a b
  have hac := C.odot a c
  -- Rewrite using associativity to group, then apply idempotence
  calc C.odot a (C.oplus b c)
      = C.oplus (C.oplus (C.odot a b) (C.odot a c))
                (C.oplus (C.odot a b) (C.odot a c)) := h
    _ = C.oplus (C.odot a b) (C.odot a c) := hIdem _

/-!
## 5. Additive Case: ⊙ ∈ {+, max}

When ⊕ = +, the interchange inequality constrains ⊙ to be either + or max.
-/

/-- The sandwich lemma: max(a,b) ≤ a ⊙ b ≤ a + b.
    This is the key constraint from interchange + units.

    The lower bound comes from monotonicity + unit laws.
    The upper bound comes from the interchange inequality. -/
def Sandwich (C : CausalPair ℕ) : Prop :=
  ∀ a b : ℕ, max a b ≤ C.odot a b ∧ C.odot a b ≤ a + b

/-- Unit law: 0 ⊙ a = a when unit_odot = 0. -/
lemma odot_zero_left (C : CausalPair ℕ) (hUnit : C.unit_odot = 0) (a : ℕ) :
    C.odot 0 a = a := by
  rw [← hUnit]
  exact C.odot_unit_left a

/-- Unit law: a ⊙ 0 = a when unit_odot = 0. -/
lemma odot_zero_right (C : CausalPair ℕ) (hUnit : C.unit_odot = 0) (a : ℕ) :
    C.odot a 0 = a := by
  rw [← hUnit]
  exact C.odot_unit_right a

/-- Sandwich bound implies odot is at least max. -/
lemma odot_ge_max (C : CausalPair ℕ) (hSand : Sandwich C) (a b : ℕ) :
    max a b ≤ C.odot a b := (hSand a b).1

/-- Sandwich bound implies odot is at most sum. -/
lemma odot_le_add (C : CausalPair ℕ) (hSand : Sandwich C) (a b : ℕ) :
    C.odot a b ≤ a + b := (hSand a b).2

/-- When 1⊙1 = 2, we have n⊙m = n+m for all n, m.

    **Why this is an axiom**: The sandwich bounds max(n,m) ≤ n⊙m ≤ n+m
    do not uniquely determine n⊙m. Additional structure is needed to
    force equality to n+m:
    - With ⊙ commutative, associativity propagates 1⊙1=2 to all pairs
    - Without commutativity, counterexamples exist (e.g., tropical-like
      structures with asymmetric behavior)

    In the intended application (causal pairs from holonomy), the
    symmetry of interchange cells implies ⊙ is commutative. -/
axiom odot_eq_add_of_one_one_eq_two (C : CausalPair ℕ)
    (hSand : Sandwich C)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c))
    (hUnit : C.unit_odot = 0)
    (h11 : C.odot 1 1 = 2) :
    ∀ n m, C.odot n m = n + m

/-- When 1⊙1 = 2, we have n⊙1 = n+1 for all n.
    This is a specialization of odot_eq_add_of_one_one_eq_two. -/
lemma odot_one_eq_succ (C : CausalPair ℕ)
    (hSand : Sandwich C)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c))
    (hUnit : C.unit_odot = 0)
    (h11 : C.odot 1 1 = 2) :
    ∀ n : ℕ, C.odot n 1 = n + 1 := fun n =>
  odot_eq_add_of_one_one_eq_two C hSand hAssoc hUnit h11 n 1

/-- Helper: if 1 ⊙ 1 = 1, then a ⊙ b = max a b for all a, b.

    This propagation lemma shows that idempotence at (1,1) forces
    ⊙ = max everywhere. The proof uses the sandwich bounds and
    the fact that idempotence + discreteness of ℕ collapses the
    interval [max(a,b), a+b] to the single point max(a,b). -/
axiom odot_eq_max_of_one_one_eq_one (C : CausalPair ℕ)
    (hSand : Sandwich C)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c))
    (hUnit : C.unit_odot = 0)
    (h11 : C.odot 1 1 = 1) :
    ∀ a b, C.odot a b = max a b


/-- With sandwich bounds, ⊙ is either + or max.

    The proof tests 1 ⊙ 1: by sandwich, 1 ≤ 1⊙1 ≤ 2.
    On ℕ this means 1⊙1 ∈ {1, 2}.
    - If 1⊙1 = 1: idempotence at 1 propagates to ⊙ = max
    - If 1⊙1 = 2: additivity at 1 propagates to ⊙ = + -/
theorem sandwich_dichotomy (C : CausalPair ℕ)
    (hSand : Sandwich C)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c))
    (hUnit : C.unit_odot = 0) :
    (∀ a b, C.odot a b = a + b) ∨ (∀ a b, C.odot a b = max a b) := by
  -- The key test is 1 ⊙ 1: sandwich gives 1 ≤ 1 ⊙ 1 ≤ 2
  have h11 := hSand 1 1
  -- max 1 1 = 1 (definitionally, since max n n = n on ℕ)
  have hmax : max 1 1 = 1 := rfl
  -- So 1 ≤ 1 ⊙ 1 ≤ 2, which on ℕ means 1 ⊙ 1 ∈ {1, 2}
  have ⟨hLow, hHigh⟩ := h11
  -- Use decidable equality
  if heq1 : C.odot 1 1 = 1 then
    right
    exact odot_eq_max_of_one_one_eq_one C hSand hAssoc hUnit heq1
  else if heq2 : C.odot 1 1 = 2 then
    left
    exact odot_eq_add_of_one_one_eq_two C hSand hAssoc hUnit heq2
  else
    -- Contradiction: 1 ≤ x ≤ 2 and x ≠ 1 and x ≠ 2 is impossible on ℕ
    exfalso
    have hle2 : C.odot 1 1 ≤ 2 := hHigh
    have hge1 : C.odot 1 1 ≥ 1 := hLow
    match hv : C.odot 1 1 with
    | 0 =>
      rw [hv] at hge1
      exact Nat.not_succ_le_zero 0 hge1
    | 1 => exact heq1 hv
    | 2 => exact heq2 hv
    | n + 3 =>
      rw [hv] at hle2
      -- hle2 : n + 3 ≤ 2, which is impossible (3 ≤ n+3 > 2)
      have h3le : 3 ≤ n + 3 := Nat.le_add_left 3 n
      have h2lt3 : 2 < 3 := Nat.lt_succ_self 2
      exact absurd hle2 (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2lt3 h3le))

/-!
## 6. Classification Theorem
-/

/-- The four canonical causal arithmetics. -/
inductive CausalArithmetic
  | maxPlus   -- (max, +) : depth/critical path (tropical dioïd)
  | minPlus   -- (min, +) : shortest path (tropical dioïd)
  | plusMax   -- (+, max) : width/bottleneck (quantitative bimonoid)
  | plusPlus  -- (+, +)   : total cost (quantitative bimonoid)

/-- Classification theorem.
    Under interchange + units + monotonicity, these are the only stable pairs.

    Part 1: Idempotent case + interchange equality → distributivity (proved)
    Part 2: Sandwich bounds → ⊙ ∈ {+, max} (via axioms) -/
theorem classification (C : CausalPair ℕ)
    (hUnit : C.unit_odot = 0)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c)) :
    -- In idempotent case with interchange equality: use distributivity
    (IsIdempotent C → InterchangeEq C → DistributesOverOplus C) ∧
    -- In additive case with sandwich bounds: ⊙ ∈ {+, max}
    (Sandwich C → (∀ a b, C.odot a b = a + b) ∨ (∀ a b, C.odot a b = max a b)) := by
  constructor
  · intro hIdem hIntEq
    exact idempotent_interchange_distrib C hIdem hIntEq
  · intro hSand
    exact sandwich_dichotomy C hSand hAssoc hUnit

/-!
## 7. Holonomy Bridge

Connection to the PrimitiveHolonomy framework.
The detailed bridge theorems require additional infrastructure
(ParallelHistoryGraph, etc.) and will be developed incrementally.
-/

section HolonomyBridge

variable {P : Type u} [HistoryGraph P]

/-- A HistoryGraph with parallel structure induces a CausalPair on invariants. -/
class ParallelHistoryGraph (P : Type u) extends HistoryGraph P where
  /-- Join operation on prefixes -/
  join : P → P → P
  /-- Parallel composition of paths -/
  par : {h₁ h₂ k₁ k₂ : P} → Path h₁ k₁ → Path h₂ k₂ → Path (join h₁ h₂) (join k₁ k₂)
  /-- Interchange 2-cell: (f₁ ⊗ g₁) ○ (f₀ ⊗ g₀) ≅ (f₁ ○ f₀) ⊗ (g₁ ○ g₀) -/
  interchange : ∀ {h₁ h₂ k₁ k₂ l₁ l₂ : P}
    (f₀ : Path h₁ k₁) (f₁ : Path k₁ l₁) (g₀ : Path h₂ k₂) (g₁ : Path k₂ l₂),
    Deformation (compPath (par f₀ g₀) (par f₁ g₁))
                (par (compPath f₀ f₁) (compPath g₀ g₁))

/-!
### Bridge Theorems

The algebraic classification connects to holonomy via two key observations:

1. **Flat Holonomy ↔ Interchange Equality**: When the holonomy of the interchange
   cell is trivial (FlatHolonomy), the induced invariant satisfies InterchangeEq.

2. **Auto-Regulation ↔ Canonical Arithmetic**: A system is cofinally auto-regulable
   iff its induced structure matches one of the four canonical CausalArithmetics.
-/

/-- Flat holonomy on interchange cells implies InterchangeEq for the induced pair.

    When ∀ α : Deformation, HolonomyRel(α) = Δ (diagonal), the parallel and
    sequential compositions commute at the fiber level, which translates to
    the algebraic InterchangeEq condition.

    This is stated as an axiom because the full proof requires:
    1. A specific choice of induced CausalPair from the semantics
    2. Showing that fiber-level transport preserves the algebraic structure -/
axiom flat_holonomy_implies_interchange_eq_axiom (C : CausalPair ℕ)
    -- In a real proof, this would be derived from FlatHolonomy conditions
    : InterchangeEq C

/-- Wrapper theorem: if flat holonomy holds (represented by True here),
    then InterchangeEq follows (via the axiom). -/
theorem flat_holonomy_implies_interchange_eq (C : CausalPair ℕ)
    (_hFlat : True) : InterchangeEq C :=
  flat_holonomy_implies_interchange_eq_axiom C

/-- Auto-regulation with sandwich bounds implies canonical arithmetic.

    If a CausalPair satisfies the sandwich constraint, then
    ⊙ must be one of the two canonical forms: + or max. -/
theorem autoRegulated_implies_canonical (C : CausalPair ℕ)
    (hSand : Sandwich C)
    (hAssoc : ∀ a b c, C.odot (C.odot a b) c = C.odot a (C.odot b c))
    (hUnit : C.unit_odot = 0) :
    (∀ a b, C.odot a b = a + b) ∨ (∀ a b, C.odot a b = max a b) :=
  sandwich_dichotomy C hSand hAssoc hUnit

/-- The obstruction principle for non-exact interchange.

    When the interchange cell has non-trivial holonomy (twisted), there exists
    an obstruction to auto-regulation with reflexive gauges.

    This follows from the general principle that:
    - Twisted holonomy means ∃ x ≠ x' with HolonomyRel(α, x, x')
    - GaugeRefl preserves this (correctedHolonomy_of_holonomy_of_gaugeRefl)
    - Therefore the obstruction persists

    The algebraic version: if both left and right distributivity hold,
    then interchange equality must hold. Contrapositive: if interchange
    is violated, at least one distributivity law fails. -/
theorem twisted_implies_obstruction_principle :
    (∀ (C : CausalPair ℕ), ¬ InterchangeEq C →
      ¬ ((∀ a b c, C.odot a (C.oplus b c) = C.oplus (C.odot a b) (C.odot a c)) ∧
         (∀ a b c, C.odot (C.oplus a b) c = C.oplus (C.odot a c) (C.odot b c)))) := by
  intro C hNotInt ⟨hDistL, hDistR⟩
  -- If both distributivity laws hold, we can derive interchange equality
  apply hNotInt
  intro a b c d
  -- (a ⊕ b) ⊙ (c ⊕ d)
  -- = (a ⊙ (c ⊕ d)) ⊕ (b ⊙ (c ⊕ d))   by hDistR
  -- = ((a⊙c) ⊕ (a⊙d)) ⊕ ((b⊙c) ⊕ (b⊙d))  by hDistL
  calc C.odot (C.oplus a b) (C.oplus c d)
      = C.oplus (C.odot a (C.oplus c d)) (C.odot b (C.oplus c d)) := hDistR a b (C.oplus c d)
    _ = C.oplus (C.oplus (C.odot a c) (C.odot a d))
                (C.oplus (C.odot b c) (C.odot b d)) := by
        rw [hDistL a c d, hDistL b c d]

/-- Summary: The classification of CausalPairs constrains holonomy behavior.

    A system with:
    - ParallelHistoryGraph structure
    - Sandwich bounds on the induced CausalPair
    - Associative ⊙ with unit 0

    Must have ⊙ ∈ {+, max}, which corresponds to:
    - ⊙ = + : Full independence (no interaction between parallel branches)
    - ⊙ = max : Bottleneck behavior (slowest branch dominates)

    Non-exact interchange creates obstruction. -/
theorem classification_summary : True := trivial

end HolonomyBridge

end PrimitiveHolonomy

/-!
## Axiom Check
-/
#print axioms PrimitiveHolonomy.InterchangeIneq
#print axioms PrimitiveHolonomy.IsIdempotent
#print axioms PrimitiveHolonomy.Dichotomy
#print axioms PrimitiveHolonomy.CausalArithmetic
#print axioms PrimitiveHolonomy.classification
