import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

/-!
# Primitive Holonomy: The 2-Geometry before Quotient

Formalization of `docs/PRIMITIVE_HOLONOMY.md`.
Strictly constructive (no `noncomputable`, no `classical`).
-/

universe u v w

/--
## 1. The Primitive: 2-Category of Histories (H₂)

We define a minimal 2-structure for histories given by:
- Objects `P`: Prefixes of histories.
- 1-Morphisms `Path`: Totals/Schedulings.
- 2-Morphisms `Deformation`: Admissible commutations/moves.

Note: We do not enforce category laws unless necessary.
-/
class HistoryGraph (P : Type u) where
  Path : P → P → Type v
  Deformation : {h k : P} → Path h k → Path h k → Prop
  idPath (h : P) : Path h h
  compPath {h k l : P} : Path h k → Path k l → Path h l

namespace PrimitiveHolonomy

variable {P : Type u}

/--
## 2. Non-Inversible Semantics: Relational Domain

Target domain: Rel(S).
-/
def Relation (A : Type u) (B : Type v) := A → B → Prop

/-- Pointwise equivalence of relations (axiom-free stand-in for relation equality). -/
def RelEq {A : Type u} {B : Type v} (R S : Relation A B) : Prop :=
  ∀ x y, R x y ↔ S x y

def relComp {A : Type u} {B : Type v} {C : Type w} (R : Relation A B) (S : Relation B C) : Relation A C :=
  fun a c ↦ ∃ b, R a b ∧ S b c

def relId {A : Type u} : Relation A A :=
  fun x y ↦ x = y

def relConverse {A : Type u} {B : Type v} (R : Relation A B) : Relation B A :=
  fun b a ↦ R a b

structure Semantics (P : Type u) [HistoryGraph P] (S : Type w) where
  /-- Transition relation for each scheduling. -/
  sem : {h k : P} → HistoryGraph.Path h k → Relation S S
  sem_id : ∀ h, sem (HistoryGraph.idPath h) = relId
  sem_comp : ∀ {h k l} (p : HistoryGraph.Path h k) (q : HistoryGraph.Path k l),
    sem (HistoryGraph.compPath p q) = relComp (sem p) (sem q)



/-- Fiber of ambiguity above `h` (relative to the observable). -/
def Fiber {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Set S :=
  { x | obs x = target_obs h }

/-- The type of points in the fiber above `h`. -/
abbrev FiberPt {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) : Type w :=
  { x : S // x ∈ Fiber (P := P) obs target_obs h }

/-- Fiber diagonal Δ_{F(h)}. -/
def FiberIdentity {S V : Type w} (obs : S → V) (target_obs : P → V) (h : P) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relId

structure LagState (Y B : Type w) where
  visible : Y
  hidden : B

def lagObs {Y B : Type w} : LagState Y B → Y := LagState.visible

theorem hidden_ne_of_ne {Y B : Type w} {target_obs : P → Y} {h : P}
    {x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h} (hx : x ≠ x') :
    x.1.hidden ≠ x'.1.hidden :=
by
  intro hhidden
  apply hx
  apply Subtype.ext
  cases x with
  | mk xs hxmem =>
    cases x' with
    | mk xs' hxmem' =>
      cases xs with
      | mk vis hid =>
        cases xs' with
        | mk vis' hid' =>
          have hvis : vis = vis' := hxmem.trans hxmem'.symm
          cases hvis
          cases hhidden
          rfl

section WithHistoryGraph

variable [HistoryGraph P]

/-- Transport restricted to fibers. -/
def Transport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs k) :=
  fun x y ↦ sem.sem p x.1 y.1

/-- Transport written in the "document style": a relation on the ambient `S`, explicitly restricted to fibers. -/
def TransportDoc {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) : Relation S S :=
  fun x y ↦ sem.sem p x y ∧ obs x = target_obs h ∧ obs y = target_obs k

theorem transport_eq_transportDoc {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) (y : FiberPt (P := P) obs target_obs k) :
  Transport sem obs target_obs p x y ↔ TransportDoc sem obs target_obs p x.1 y.1 :=
by
  -- `x.2` and `y.2` are exactly the fiber equalities.
  simpa [Transport, TransportDoc, Fiber, FiberPt] using
    (show sem.sem p x.1 y.1 ↔ sem.sem p x.1 y.1 ∧ obs x.1 = target_obs h ∧ obs y.1 = target_obs k from
      ⟨fun hp ↦ ⟨hp, x.2, y.2⟩, fun hdoc ↦ hdoc.1⟩)

/-- Defines holonomy relative to a 2-cell. -/
def HolonomyRel {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relComp (Transport sem obs target_obs p) (relConverse (Transport sem obs target_obs q))

theorem holonomy_congr {S : Type w} {V : Type w}
    (sem₁ sem₂ : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (Hp : Transport sem₁ obs target_obs p = Transport sem₂ obs target_obs p)
    (Hq : Transport sem₁ obs target_obs q = Transport sem₂ obs target_obs q) :
    HolonomyRel sem₁ obs target_obs α = HolonomyRel sem₂ obs target_obs α := by
  unfold HolonomyRel
  rw [← Hp, ← Hq]

theorem holonomy_def {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : FiberPt (P := P) obs target_obs h) :
  HolonomyRel sem obs target_obs α x x' ↔
  ∃ y : FiberPt (P := P) obs target_obs k,
    Transport sem obs target_obs p x y ∧ Transport sem obs target_obs q x' y :=
by rfl

/-!
## 5. "Lag" (Delayed Repercussion)
-/
/-- `x` is compatible with the observed value at `k` along `p` iff `p` can reach the fiber at `k` from `x`. -/
def Compatible {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) : Prop :=
  ∃ y : FiberPt (P := P) obs target_obs k, Transport sem obs target_obs p x y

/-- Lag event: two distinct states are related by holonomy now, but only one stays compatible later. -/
def LagEvent {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop :=
  ∃ x x' : FiberPt (P := P) obs target_obs h,
    x ≠ x' ∧ HolonomyRel sem obs target_obs α x x' ∧
    Compatible sem obs target_obs step x ∧ ¬ Compatible sem obs target_obs step x'

theorem lag_of_witness {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (x x' : FiberPt (P := P) obs target_obs h)
    (hx : x ≠ x')
    (hHol : HolonomyRel sem obs target_obs α x x')
    (hstep : Compatible sem obs target_obs step x ∧ ¬ Compatible sem obs target_obs step x') :
    LagEvent sem obs target_obs α step :=
by
  refine ⟨x, x', hx, hHol, hstep.1, hstep.2⟩

/--
Step-dependence on the hidden component (product scenario `X = Y×B`, `O(y,b)=y`):
two states in the same fiber with different `hidden` values cannot both remain compatible
with the same observed next step.
-/
def StepDependsOnHidden {Y B : Type w} (sem : Semantics P (LagState Y B))
    (target_obs : P → Y) {h k : P} (step : HistoryGraph.Path h k) : Prop :=
  ∀ x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h,
    x.1.hidden ≠ x'.1.hidden →
      ¬ (Compatible sem lagObs target_obs step x ∧ Compatible sem lagObs target_obs step x')

theorem lag_of_twist_and_hidden_step
    {Y B : Type w} (sem : Semantics P (LagState Y B)) (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (hDep : StepDependsOnHidden (P := P) sem target_obs step)
    (x x' : FiberPt (P := P) (obs := (lagObs (Y := Y) (B := B))) target_obs h)
    (hx : x ≠ x')
    (hHol : HolonomyRel sem lagObs target_obs α x x')
    (hCompat : Compatible sem lagObs target_obs step x) :
    LagEvent sem lagObs target_obs α step :=
by
  have hHidden : x.1.hidden ≠ x'.1.hidden := hidden_ne_of_ne (P := P) (x := x) (x' := x') hx
  have hNotCompat : ¬ Compatible sem lagObs target_obs step x' := by
    intro hx'
    exact (hDep x x' hHidden) ⟨hCompat, hx'⟩
  exact lag_of_witness (P := P) sem lagObs target_obs α step x x' hx hHol ⟨hCompat, hNotCompat⟩

/--
## 6. Auto-Regulation "Cofinal"

Formalization of the repair condition on a set of 2-cells J.

Audit Reform: Gauge is a "Fiber Preserving Repair".
Ideally it maps Fiber(k) to Fiber(k).
We define a predicate `IsFiberPreserving`.
-/
def Gauge {S V : Type w} (obs : S → V) (target_obs : P → V) :=
  {h k : P} → HistoryGraph.Path h k →
    Relation (FiberPt (P := P) obs target_obs k) (FiberPt (P := P) obs target_obs k)

/-- Corrected transport along a total p: first do Transport, then apply the gauge at the target. -/
def CorrectedTransport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs) (p : HistoryGraph.Path h k) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs k) :=
  relComp (Transport sem obs target_obs p) (gauge p)

/-- Corrected holonomy: Hol♯(p,q) = T♯_p ∘ (T♯_q)†  -/
def CorrectedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge (P := P) obs target_obs) {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) :
    Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h) :=
  relComp (CorrectedTransport sem obs target_obs gauge p)
          (relConverse (CorrectedTransport sem obs target_obs gauge q))

/-- A primitive 2-cell: (h,k,p,q) together with α : p ⇒ q. We use PLift to put Prop in Type. -/
abbrev Cell {P : Type u} [HistoryGraph P] :=
  Σ h k : P, Σ p q : HistoryGraph.Path h k, PLift (HistoryGraph.Deformation p q)

/-- Source prefix of a 2-cell. -/
def CellSrc {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨h, _, _, _, _⟩ => h

/-- Target prefix of a 2-cell. -/
def CellTgt {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨_, k, _, _, _⟩ => k

/-- “c lives in J” means its endpoints are in `J`. -/
def CellLivesIn {P : Type u} [HistoryGraph P] (J : Set P) (c : Cell (P := P)) : Prop :=
  CellSrc c ∈ J ∧ CellTgt c ∈ J

/-- Set of 2-cells whose endpoints lie in `J`. -/
def CellsOver (C : Set P) : Set (Cell (P := P)) :=
  { c | CellSrc c ∈ C ∧ CellTgt c ∈ C }

/-- Holonomy is weak iff Δ ⊆ Hol. -/
def WeakHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x : FiberPt (P := P) obs target_obs h, HolonomyRel sem obs target_obs α x x

/-- Holonomy is flat (strong) iff Hol = Δ. -/
def FlatHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x x' : FiberPt (P := P) obs target_obs h, HolonomyRel sem obs target_obs α x x' ↔ x = x'

/-- Holonomy is twisted iff ∃ x ≠ x' with (x,x') ∈ Hol. -/
def TwistedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∃ x x' : FiberPt (P := P) obs target_obs h, x ≠ x' ∧ HolonomyRel sem obs target_obs α x x'

/--
Definition of Auto-Regulation on a set J of deformations.
"There exists a fiber-preserving gauge φ such that for all α ∈ J, the corrected holonomy is the diagonal."
-/
def AutoRegulated {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge (P := P) obs target_obs,
    ∀ c, c ∈ J →
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x',
        CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'

/--
## 7. Constructive Verification
-/
theorem is_constructive : True := trivial

/- 1) Préordre interne des préfixes : h ≤ k ssi Reach h k (∃ total). -/
def Reach (h k : P) : Prop :=
  Nonempty (HistoryGraph.Path h k)

theorem reach_refl (h : P) : Reach h h :=
  ⟨HistoryGraph.idPath h⟩

theorem reach_trans {h k l : P} : Reach h k → Reach k l → Reach h l :=
by
  intro hk kl
  rcases hk with ⟨p⟩
  rcases kl with ⟨q⟩
  exact ⟨HistoryGraph.compPath p q⟩

/- 2) Cofinalité (futur ouvert interne) sur (P, Reach). -/
def Cofinal (C : Set P) : Prop :=
  ∀ h : P, ∃ k : P, k ∈ C ∧ Reach h k

/- 3) Dirigé + inférieur-clos : idéal (exécution prolongée comme futur dirigé). -/
def LowerClosed (I : Set P) : Prop :=
  ∀ {h k : P}, Reach h k → k ∈ I → h ∈ I

def Directed (I : Set P) : Prop :=
  ∀ ⦃a b : P⦄, a ∈ I → b ∈ I → ∃ c : P, c ∈ I ∧ Reach a c ∧ Reach b c

structure Ideal (I : Set P) : Prop where
  (lower : LowerClosed I)
  (dir   : Directed I)

/- 4) Temps/ordinal = shadow : un scheduling est une chaîne cofinale. -/
structure Scheduling (A : Type) [Preorder A] where
  c : A → P
  mono : ∀ {i j : A}, i ≤ j → Reach (c i) (c j)
  cofinal : ∀ h : P, ∃ i : A, Reach h (c i)

/- 5) Auto-régulation cofinale : on restreint les 2-cellules à un futur cofinal. -/

-- Rappel : AutoRegulated est déjà défini chez toi.
-- On ajoute la version “cofinalement” :
def AutoRegulatedCofinal
  {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ AutoRegulated sem obs target_obs (CellsOver C)

end WithHistoryGraph

end PrimitiveHolonomy



#print axioms PrimitiveHolonomy.holonomy_congr
#print axioms PrimitiveHolonomy.holonomy_def
#print axioms PrimitiveHolonomy.lag_of_witness
#print axioms PrimitiveHolonomy.Compatible
#print axioms PrimitiveHolonomy.Transport
#print axioms PrimitiveHolonomy.LagEvent
#print axioms PrimitiveHolonomy.AutoRegulated
#print axioms PrimitiveHolonomy.Reach
#print axioms PrimitiveHolonomy.Cofinal
#print axioms PrimitiveHolonomy.Scheduling
#print axioms PrimitiveHolonomy.AutoRegulatedCofinal

namespace PrimitiveHolonomy

universe uQ

/-- 1D shot: compress each total/scheduling `p : Path h k` into a code in `Q`. -/
abbrev Summary {P : Type u} [HistoryGraph P] (Q : Type uQ) :=
  ∀ {h k : P}, HistoryGraph.Path h k → Q

/-- Holonomy factors through a 1D summary `q` iff there exists a map `H`
    such that Hol(α) depends only on the two 1D codes of the paths involved in α. -/
def FactorsHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {Q : Type uQ} (q : Summary (P := P) Q) : Prop :=
  ∃ H : ∀ h : P, Q → Q →
        Relation (FiberPt (P := P) obs target_obs h) (FiberPt (P := P) obs target_obs h),
    ∀ (c : Cell (P := P)),
      let ⟨h, _, p, q', ⟨α⟩⟩ := c
      RelEq (HolonomyRel sem obs target_obs α) (H h (q p) (q q'))

/-- Forward direction: if holonomy factors through a 1D summary,
    then equal codes force equal holonomy. -/
theorem factors_eq_of_codes
  {P : Type u} [HistoryGraph P] {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  {Q : Type uQ} (q : Summary (P := P) Q)
  (fact : FactorsHolonomy (P := P) sem obs target_obs q)
  {h k : P}
  {p₁ q₁ : HistoryGraph.Path h k} (α₁ : HistoryGraph.Deformation p₁ q₁)
  {p₂ q₂ : HistoryGraph.Path h k} (α₂ : HistoryGraph.Deformation p₂ q₂)
  (hp : q p₁ = q p₂) (hq : q q₁ = q q₂) :
  RelEq (HolonomyRel (P := P) sem obs target_obs α₁)
        (HolonomyRel (P := P) sem obs target_obs α₂) :=
by
  rcases fact with ⟨H, Hfact⟩
  let c1 : Cell (P := P) := ⟨h, k, p₁, q₁, ⟨α₁⟩⟩
  let c2 : Cell (P := P) := ⟨h, k, p₂, q₂, ⟨α₂⟩⟩
  have e1 : RelEq (HolonomyRel (P := P) sem obs target_obs α₁) (H h (q p₁) (q q₁)) := Hfact c1
  have e2 : RelEq (HolonomyRel (P := P) sem obs target_obs α₂) (H h (q p₂) (q q₂)) := Hfact c2
  intro x x'
  have h1 : HolonomyRel (P := P) sem obs target_obs α₁ x x' ↔ H h (q p₁) (q q₁) x x' := e1 x x'
  have h2 : HolonomyRel (P := P) sem obs target_obs α₂ x x' ↔ H h (q p₂) (q q₂) x x' := e2 x x'
  have hmid : H h (q p₁) (q q₁) x x' ↔ H h (q p₂) (q q₂) x x' := by
    rw [hp, hq]
  exact h1.trans (hmid.trans h2.symm)

/-- Witness-killer: if two 2-cells have the same limit codes but different holonomy,
    then NO factorization through that 1D shot exists. -/
theorem witness_no_factor {P : Type u} [HistoryGraph P] {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  {Q : Type uQ} (q : Summary (P := P) Q)
  {h k : P}
  -- Two deformations
  {p₁ q₁ : HistoryGraph.Path h k} (α₁ : HistoryGraph.Deformation p₁ q₁)
  {p₂ q₂ : HistoryGraph.Path h k} (α₂ : HistoryGraph.Deformation p₂ q₂)
  -- Codes match strictly
  (hp : q p₁ = q p₂) (hq : q q₁ = q q₂)
  -- Holonomies differ
  (hne : ¬ RelEq (HolonomyRel sem obs target_obs α₁) (HolonomyRel sem obs target_obs α₂)) :
  ¬ FactorsHolonomy sem obs target_obs q :=
by
  intro fact
  exact hne (factors_eq_of_codes (P := P) sem obs target_obs q fact (α₁ := α₁) (α₂ := α₂) hp hq)

/-- Global non-reduction statement (for holonomy itself): no 1D shot can capture it. -/
def NonReducibleHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (Q : Type uQ) (q : Summary (P := P) Q),
    ¬ FactorsHolonomy sem obs target_obs q

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.factors_eq_of_codes
#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.NonReducibleHolonomy
