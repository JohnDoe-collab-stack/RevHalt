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

variable {P : Type u} [HistoryGraph P]

/--
## 2. Non-Inversible Semantics: Relational Domain

Target domain: Rel(S).
-/
def Relation (S : Type w) := S → S → Prop

def relComp {S : Type w} (R1 R2 : Relation S) : Relation S :=
  fun x z ↦ ∃ y, R1 x y ∧ R2 y z

def relId {S : Type w} : Relation S :=
  fun x y ↦ x = y

def relConverse {S : Type w} (R : Relation S) : Relation S :=
  fun x y ↦ R y x

structure Semantics (P : Type u) [HistoryGraph P] (S : Type w) where
  /-- Reachable states for each history prefix. -/
  obj : P → Set S
  /-- Transition relation for each scheduling. -/
  sem : {h k : P} → HistoryGraph.Path h k → Relation S
  /-- Consistency: Transitions only occur between reachable states. -/
  sem_dom : ∀ {h k} (p : HistoryGraph.Path h k) x y, sem p x y → x ∈ obj h ∧ y ∈ obj k
  sem_id : ∀ h, sem (HistoryGraph.idPath h) = relId
  sem_comp : ∀ {h k l} (p : HistoryGraph.Path h k) (q : HistoryGraph.Path k l),
    sem (HistoryGraph.compPath p q) = relComp (sem p) (sem q)



/-- The fiber is the set of *reachable* states compatible with the observation. -/
def Fiber {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V) (h : P) : Set S :=
  { x | x ∈ sem.obj h ∧ obs x = target_obs h }

/-- Transport restricted to fibers. -/
def Transport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (p : HistoryGraph.Path h k) : Relation S :=
  fun x y ↦ sem.sem p x y ∧ x ∈ Fiber sem obs target_obs h ∧ y ∈ Fiber sem obs target_obs k

/-- Defines holonomy relative to a 2-cell. -/
def HolonomyRel {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) : Relation S :=
  relComp (Transport sem obs target_obs p) (relConverse (Transport sem obs target_obs q))

theorem holonomy_def {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) (x x' : S) :
  HolonomyRel sem obs target_obs α x x' ↔
  ∃ y, Transport sem obs target_obs p x y ∧ Transport sem obs target_obs q x' y :=
by rfl

/--
## 5. "Lag" (Delayed Repercussion)
-/
structure LagState (Y B : Type w) where
  visible : Y
  hidden : B

def lagObs {Y B : Type w} : LagState Y B → Y := LagState.visible

/--
## 6. Auto-Regulation "Cofinal"

Formalization of the repair condition on a set of 2-cells J.

Audit Reform: Gauge is a "Fiber Preserving Repair".
Ideally it maps Fiber(k) to Fiber(k).
We define a predicate `IsFiberPreserving`.
-/
def Gauge (P : Type u) [HistoryGraph P] (S : Type w) :=
  {h k : P} → HistoryGraph.Path h k → Relation S

def IsFiberPreserving {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (G : Gauge P S) : Prop :=
  ∀ {h k} (p : HistoryGraph.Path h k) x y,
    G p x y → x ∈ Fiber sem obs target_obs k ∧ y ∈ Fiber sem obs target_obs k

/-- Corrected transport along a total p: first do Transport, then apply the gauge at the target. -/
def CorrectedTransport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge P S) (p : HistoryGraph.Path h k) : Relation S :=
  relComp (Transport sem obs target_obs p) (gauge p)

/-- Corrected holonomy: Hol♯(p,q) = T♯_p ∘ (T♯_q)†  -/
def CorrectedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge P S) {p q : HistoryGraph.Path h k} (_α : HistoryGraph.Deformation p q) : Relation S :=
  relComp (CorrectedTransport sem obs target_obs gauge p)
          (relConverse (CorrectedTransport sem obs target_obs gauge q))

/-- A primitive 2-cell: (h,k,p,q) together with α : p ⇒ q. We use PLift to put Prop in Type. -/
abbrev Cell {P : Type u} [HistoryGraph P] :=
  Σ h k : P, Σ p q : HistoryGraph.Path h k, PLift (HistoryGraph.Deformation p q)

/-- Fiber diagonal (enough as-is constructively). -/
def FiberIdentity {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V) {h : P} : Relation S :=
  fun x y ↦ x = y ∧ x ∈ Fiber sem obs target_obs h

/--
Definition of Auto-Regulation on a set J of deformations.
"There exists a fiber-preserving gauge φ such that for all α ∈ J, the corrected holonomy is the diagonal."
-/
def AutoRegulated {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge P S,
    IsFiberPreserving sem obs target_obs φ ∧
    ∀ c, c ∈ J →
      let ⟨h, _, _, _, ⟨α⟩⟩ := c
      CorrectedHolonomy sem obs target_obs φ α
        = FiberIdentity sem obs target_obs (h := h)

/--
## 7. Constructive Verification
-/
theorem is_constructive : True := trivial

/- 1) Préordre interne des préfixes : h ≤ k ssi Reach h k (∃ total). -/
def Reach (h k : P) : Prop :=
  ∃ _ : HistoryGraph.Path h k, True

theorem reach_refl (h : P) : Reach h h :=
  ⟨HistoryGraph.idPath h, trivial⟩

theorem reach_trans {h k l : P} : Reach h k → Reach k l → Reach h l :=
by
  intro hk kl
  rcases hk with ⟨p, _⟩
  rcases kl with ⟨q, _⟩
  exact ⟨HistoryGraph.compPath p q, trivial⟩

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

def CellSrc {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨h, _, _, _, _⟩ => h

def CellTgt {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨_, k, _, _, _⟩ => k

def CellsOver (C : Set P) : Set (Cell (P := P)) :=
  { c | CellSrc c ∈ C ∧ CellTgt c ∈ C }

-- Rappel : AutoRegulated est déjà défini chez toi.
-- On ajoute la version “cofinalement” :
def AutoRegulatedCofinal
  {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ AutoRegulated sem obs target_obs (CellsOver C)

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.holonomy_def
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
  ∃ H : Q → Q → Relation S,
    ∀ (c : Cell (P := P)),
      let ⟨_, _, p, q', ⟨α⟩⟩ := c
      HolonomyRel sem obs target_obs α = H (q p) (q q')

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
  (hne : HolonomyRel sem obs target_obs α₁ ≠ HolonomyRel sem obs target_obs α₂) :
  ¬ FactorsHolonomy sem obs target_obs q :=
by
  intro fact
  rcases fact with ⟨H, Hfact⟩
  -- Apply factorization to both cells
  let c1 : Cell (P := P) := ⟨h, k, p₁, q₁, ⟨α₁⟩⟩
  let c2 : Cell (P := P) := ⟨h, k, p₂, q₂, ⟨α₂⟩⟩
  have e1 : HolonomyRel sem obs target_obs α₁ = H (q p₁) (q q₁) := Hfact c1
  have e2 : HolonomyRel sem obs target_obs α₂ = H (q p₂) (q q₂) := Hfact c2
  -- Rewrite and contradict
  have : HolonomyRel sem obs target_obs α₁ = HolonomyRel sem obs target_obs α₂ := by
    rw [e1, e2, hp, hq]
  exact hne this

/-- Global non-reduction statement (for holonomy itself): no 1D shot can capture it. -/
def NonReducibleHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (Q : Type uQ) (q : Summary (P := P) Q),
    ¬ FactorsHolonomy sem obs target_obs q

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.NonReducibleHolonomy
