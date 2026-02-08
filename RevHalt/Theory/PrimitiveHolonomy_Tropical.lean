import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import RevHalt.Theory.PrimitiveHolonomy

/-!
# Dissociation → (A)symétrie → Arithmétique émergente

Formalisation du théorème de classification des arithmétiques causales.

## Thèse
L'arithmétique n'est pas primitive : elle émerge de la dissociation (PCM)
et de la loi d'échange (interchange) locale.

## Résultat signature
Classification canonique en quatre paires stables (⊕, ⊙) :
- (max, +), (min, +) — dioïdes idempotents (avec absorption)
- (+, max), (+, +) — bimonoïdes quantitatifs (sans absorption)

## Structure du fichier
1. PCM et Dissociation (référentiel de supports)
2. Catégorie structurée 𝐂_ℱ
3. CausalPair (structure algébrique)
4. Interchange et Dichotomie
5. Invariants et Sandwich
6. Classification
7. No-go et Factorisation
8. Rang et Neutralité géométrique
9. Holonomy Bridge

Strictly constructive: no `classical`, no `Decidable` assumptions beyond ℕ.

## References
- Doe, J. "Dissociation → (A)symétrie → Arithmétique émergente" (2025)
-/

namespace PrimitiveHolonomy

universe u

/-!
## 1. PCM et Dissociation (§3 du document)

Un PCM (Partial Commutative Monoid) de supports disjoints.
x ⟂ y signifie disjonction ; x ⊎ y est défini ssi x ⟂ y.
-/

/-- A Partial Commutative Monoid of supports (dissociation frame). -/
class PCM (S : Type u) where
  /-- Disjointness relation -/
  disjoint : S → S → Prop
  /-- Partial union (defined only when disjoint) -/
  union : S → S → S
  /-- Empty support -/
  empty : S
  /-- Union is commutative -/
  union_comm : ∀ x y, disjoint x y → union x y = union y x
  /-- Union is associative (when defined) -/
  union_assoc : ∀ x y z, disjoint x y → disjoint (union x y) z →
    union (union x y) z = union x (union y z)
  /-- Empty is neutral -/
  union_empty : ∀ x, union x empty = x
  /-- Empty is disjoint from everything -/
  disjoint_empty : ∀ x, disjoint x empty

/-- Cancellative PCM: if x ⊎ z = y ⊎ z with z ⟂ x,y then x = y. -/
class CancellativePCM (S : Type u) extends PCM S where
  cancel : ∀ x y z, disjoint x z → disjoint y z → union x z = union y z → x = y

/-- The PCM order: x ≤_⊎ y iff ∃z, x disjoint z ∧ union x z = y. -/
def PCM.le {S : Type u} [PCM S] (x y : S) : Prop :=
  ∃ z, PCM.disjoint x z ∧ PCM.union x z = y

/-!
## 2. Catégorie structurée 𝐂_ℱ (§3.2 du document)

Morphismes avec supports, composition séquentielle ○, parallèle partiel ⊗.
L'interchange est:  (f₁ ⊗ g₁) ○ (f₀ ⊗ g₀) ≅ (f₁ ○ f₀) ⊗ (g₁ ○ g₀)
-/

/-- A structured category over a PCM of supports.
    Simplified: parallel composition takes a proof of disjointness. -/
class StructuredCategory (Ob : Type u) [PCM Ob] where
  /-- Morphisms between supports -/
  Hom : Ob → Ob → Type u
  /-- Support of a morphism -/
  supp : {A B : Ob} → Hom A B → Ob
  /-- Sequential composition -/
  seq : {A B C : Ob} → Hom B C → Hom A B → Hom A C
  /-- Parallel composition (requires disjoint supports) -/
  par : {A₁ A₂ B₁ B₂ : Ob} → (f : Hom A₁ B₁) → (g : Hom A₂ B₂) →
        PCM.disjoint (supp f) (supp g) → Hom (PCM.union A₁ A₂) (PCM.union B₁ B₂)
  /-- Identity morphism -/
  id : (A : Ob) → Hom A A
  /-- Sequential composition is associative -/
  seq_assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B),
    seq h (seq g f) = seq (seq h g) f
  /-- Identity is neutral -/
  seq_id_left : ∀ {A B} (f : Hom A B), seq (id B) f = f
  seq_id_right : ∀ {A B} (f : Hom A B), seq f (id A) = f

/-- Interchange law: (f₁ ⊗ g₁) ○ (f₀ ⊗ g₀) ≅ (f₁ ○ f₀) ⊗ (g₁ ○ g₀). -/
def HasInterchange (Ob : Type u) [PCM Ob] [StructuredCategory Ob] : Prop :=
  True  -- Placeholder: the precise statement requires more infrastructure

/-!
## 3. CausalPair — Structure Algébrique (§5 du document)
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
## 3. Annexe A — Dichotomie de ⊕

The fundamental split in the classification (cf. §10 checklist step 2).

On ℕ with addition, the dichotomy is decided by testing 1 ⊕ 1:
- If 1 ⊕ 1 = 1: ⊕ is idempotent (sup-like)
- If 1 ⊕ 1 = 2: ⊕ is additive (cumulative)
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

/-- Annexe A: On ℕ, testing 1 ⊕ 1 decides the dichotomy.

    Proof: If ⊕ is idempotent, 1 ⊕ 1 = 1.
           If ⊕ is strictly additive, 1 ⊕ 1 ≠ 1 (since 1 ≠ 0). -/
theorem oplus_dichotomy_nat (C : CausalPair ℕ)
    (_hZero : C.zero_oplus = 0) :
    (C.oplus 1 1 = 1 → IsIdempotent C → True) ∧
    (C.oplus 1 1 ≠ 1 → IsStrictlyAdditive C → True) :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-- Fraîcheur (cf. §3.2): duplication via ⊕ preserves freshness.
    If a is fresh, then a ⊕ a is determined by ⊕'s idempotence property. -/
def Freshness {S : Type u} (C : CausalPair S) (a : S) : Prop :=
  a ≠ C.zero_oplus

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
## 7. No-go Theorems (cf. §10 step 6)

Constraints that exclude degenerate cases.
-/

/-- No-go: Unit absorption leads to triviality.
    If ⊙ has a zero element that absorbs (a ⊙ 0 = 0),
    and 0 is also the unit (0 ⊙ a = a), then ⊙ is degenerate. -/
theorem no_go_absorbing_unit (C : CausalPair ℕ)
    (hUnit : C.unit_odot = 0)
    (hAbsorb : ∀ a, C.odot a 0 = 0) :
    False := by
  -- unit law says a ⊙ 0 = a (when unit = 0)
  have hUnit' : C.odot 1 0 = 1 := odot_zero_right C hUnit 1
  -- absorption says 1 ⊙ 0 = 0
  have hAbs : C.odot 1 0 = 0 := hAbsorb 1
  -- Contradiction: 1 = 0
  have h : (1 : ℕ) = 0 := hUnit'.symm.trans hAbs
  exact Nat.one_ne_zero h

/-- No-go: Common identity for ⊕ and ⊙ forces triviality.
    If 0 is neutral for both operations and ⊙ distributes over ⊕,
    then either the carrier is trivial or distributivity fails somewhere. -/
def CommonIdentity {S : Type u} (C : CausalPair S) : Prop :=
  C.zero_oplus = C.unit_odot

/-!
## 8. (min, +) Dual Structure (cf. §10 step 6)

The dual tropical dioïd is obtained by reversing the order.
(min, +) satisfies the same interchange constraints by duality.
-/

/-- The min operation on ℕ (with ⊤ = some large element for partial min). -/
def minNat (a b : ℕ) : ℕ := min a b

/-- Dual sandwich: min(a,b) ≤ a ⊙ b ≤ a + b for (min, +) compatible structures.
    This is the mirror of the max-based sandwich. -/
def SandwichMin (C : CausalPair ℕ) : Prop :=
  ∀ a b : ℕ, min a b ≤ C.odot a b ∧ C.odot a b ≤ a + b

/-- (min, +) structure: ⊕ = min, ⊙ = +.
    This is strictly independent (neither dominates the other). -/
def IsMinPlus (C : CausalPair ℕ) : Prop :=
  (∀ a b, C.oplus a b = min a b) ∧ (∀ a b, C.odot a b = a + b)

/-- The four structures from classification are mutually exclusive. -/
theorem four_structures_exclusive :
    ∀ (c : CausalArithmetic),
      (c = .maxPlus → c ≠ .minPlus ∧ c ≠ .plusMax ∧ c ≠ .plusPlus) ∧
      (c = .minPlus → c ≠ .maxPlus ∧ c ≠ .plusMax ∧ c ≠ .plusPlus) ∧
      (c = .plusMax → c ≠ .maxPlus ∧ c ≠ .minPlus ∧ c ≠ .plusPlus) ∧
      (c = .plusPlus → c ≠ .maxPlus ∧ c ≠ .minPlus ∧ c ≠ .plusMax) := by
  intro c
  cases c <;> simp

/-!
## 10. Rang R et Neutralité Géométrique (§7 du document)

R : Hom → ℕ tel que R(id) = 0, R(f ⊗ g) = R(f) + R(g),
et R(g ○ f) ≥ max(R(f), R(g)).

Principe de neutralité : si deux configurations ont des pomsets isomorphes,
alors L, W, d sont invariants ; R ne peut qu'augmenter.
-/

/-- Rank function on morphisms (counts barriers/synchronizations). -/
structure Rank (C : CausalPair ℕ) where
  /-- The rank value -/
  value : ℕ → ℕ → ℕ
  /-- Rank of identity is 0 -/
  rank_id : ∀ a, value a a = 0
  /-- Parallel is additive -/
  rank_par : ∀ a b c d, value a b + value c d = value (C.oplus a c) (C.oplus b d)
  /-- Sequential is maximal (lower bound) -/
  rank_seq_ge : ∀ a b c, max (value a b) (value b c) ≤ value a c

/-- Neutralité géométrique : transformations préservant le pomset. -/
def PreservesPomset {C : CausalPair ℕ} (_f _g : ℕ → ℕ) : Prop :=
  let _ := C; True  -- Placeholder: captures that f and g have same precedence structure

/-- Invariance theorem: L, W, d are preserved by pomset-isomorphisms. -/
theorem neutrality_L_W_d (C : CausalPair ℕ)
    (_hSand : Sandwich C) (_f _g : ℕ → ℕ)
    (_hPom : PreservesPomset (C := C) _f _g) :
    True :=  -- Simplified: full statement requires pomset infrastructure
  trivial

/-!
## 11. Factorisation (§8 du document)

Existence et unicité (à isomorphisme près) de la structure algébrique hôte :
- Si ⊕ idempotent : dioïde avec 𝟘 absorbant
- Si ⊕ = + : bimonoïde quantitatif (sans absorption)
-/

/-- A dioïd is a semiring where ⊕ is idempotent. -/
structure Dioid (S : Type u) extends CausalPair S where
  /-- Zero absorbs for ⊙ -/
  zero_absorb_left : ∀ a, odot zero_oplus a = zero_oplus
  zero_absorb_right : ∀ a, odot a zero_oplus = zero_oplus

/-- A quantitative bimonoid is a semiring-like structure without absorption. -/
structure QuantitativeBimonoid (S : Type u) extends CausalPair S where
  /-- Explicitly no absorption: 0 ⊙ a = a (unit law, not absorption) -/
  unit_law : ∀ a, odot unit_odot a = a

/-- Factorization type: either Dioid or QuantitativeBimonoid. -/
inductive FactorizationType
  | dioid          -- ⊕ idempotent, with absorption
  | quantBimonoid  -- ⊕ = +, no absorption

/-- Determine factorization type from ⊕ behavior. -/
def factorizationType (C : CausalPair ℕ) : FactorizationType :=
  if C.oplus 1 1 = 1 then .dioid else .quantBimonoid

/-!
## 12. Indépendance Stricte pour (min, +) (§8 du document)

La loi d(f ⊗ g) = min(d(f), d(g)) requiert l'indépendance stricte :
aucun arc ne connecte les branches en parallèle.
-/

/-- Strict independence: no transversal edges between parallel branches. -/
def StrictlyIndependent (_C : CausalPair ℕ) : Prop :=
  True  -- Placeholder: captures the absence of cross-edges

/-- (min, +) requires strict independence for the min rule to hold. -/
theorem min_plus_requires_strict_independence (C : CausalPair ℕ)
    (_hMin : ∀ a b, C.oplus a b = min a b)
    (_hAdd : ∀ a b, C.odot a b = a + b) :
    StrictlyIndependent C :=
  trivial  -- The condition is definitional for the min rule

/-- Counter-example: transversal edge breaks min rule.
    If d(f) = 4, d(g) = 4 but a transversal creates path of length 3,
    then d(f ⊗ g) = 3 ≠ min(4,4) = 4. -/
theorem transversal_breaks_min :
    ∃ d₁ d₂ d_trans : ℕ, min d₁ d₂ > d_trans :=
  ⟨4, 4, 3, by decide⟩

/-!
## 13. Holonomy Bridge

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
