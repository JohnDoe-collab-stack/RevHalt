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

/-- Defines holonomy relative to a 2-cell witness. -/
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
To ensure this intrinsically, CorrectedTransport enforces the target fiber constraint.
-/
def Gauge (P : Type u) [HistoryGraph P] (S : Type w) :=
  {h k : P} → HistoryGraph.Path h k → Relation S

/-- Corrected transport: T♯_p = T_p ;; (Gauge_p ∩ TargetFiber_k).
    This forces the gauge to only be valid if it lands in the fiber. -/
def CorrectedTransport {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge P S) (p : HistoryGraph.Path h k) : Relation S :=
  fun x y ↦ (relComp (Transport sem obs target_obs p) (gauge p) x y)
          ∧ y ∈ Fiber sem obs target_obs k

/-- Corrected holonomy: Hol♯(p,q) = T♯_p ∘ (T♯_q)†  -/
def CorrectedHolonomy {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (gauge : Gauge P S) {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Relation S :=
  relComp (CorrectedTransport sem obs target_obs gauge p)
          (relConverse (CorrectedTransport sem obs target_obs gauge q))

/-- A primitive 2-cell: (h,k,p,q) together with α : p ⇒ q. We use PLift to put Prop in Type. -/
abbrev Cell {P : Type u} [HistoryGraph P] :=
  Σ h k : P, Σ p q : HistoryGraph.Path h k, PLift (HistoryGraph.Deformation p q)

/-- Strict Fiber Identity: Diagonal constrained to the fiber. -/
def FiberIdentity {S V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V) {h : P} : Relation S :=
  fun x y ↦ x = y ∧ x ∈ Fiber sem obs target_obs h ∧ y ∈ Fiber sem obs target_obs h

/--
Definition of Auto-Regulation on a set J of deformations.
"There exists a gauge φ such that... corrected holonomy is the diagonal."
Fiber preservation is now intrinsic to CorrectedTransport.
-/
def AutoRegulated {S : Type w} {V : Type w} (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge P S,
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

/- 5) Auto-régulation cofinale : on restreint les 2-cellules à un idéal cofinal. -/

def CellSrc {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨h, _, _, _, _⟩ => h

def CellTgt {P : Type u} [HistoryGraph P] : Cell (P := P) → P
| ⟨_, k, _, _, _⟩ => k

def CellsOver (C : Set P) : Set (Cell (P := P)) :=
  { c | CellSrc c ∈ C ∧ CellTgt c ∈ C }

/--
AutoRegulatedCofinal now requires the existence of a *Cofinal Ideal* C (pertinent future).
-/
def AutoRegulatedCofinal
  {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Ideal C ∧ Cofinal C ∧ AutoRegulated sem obs target_obs (CellsOver C)

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

/--
AdmissibleSummary: Restrict the summary to valid 1D shadows.
A valid 1D shadow must be invariant under deformations (2-cells).
This captures the idea that the 1D view "quotients out" the 2-geometry.
-/
def AdmissibleSummary {P : Type u} [HistoryGraph P] {Q : Type uQ} (q : Summary (P := P) Q) : Prop :=
  ∀ {h k : P} {p q' : HistoryGraph.Path h k},
    HistoryGraph.Deformation p q' → q p = q q'

/-- Holonomy factors through a 1D summary `q` iff there exists a map `H`
    such that Hol(α) depends only on the two 1D codes of the paths involved in α. -/
def FactorsHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    {Q : Type uQ} (q : Summary (P := P) Q) : Prop :=
  ∃ H : Q → Q → Relation S,
    ∀ (c : Cell (P := P)),
      let ⟨_, _, p, q', ⟨α⟩⟩ := c
      HolonomyRel sem obs target_obs α = H (q p) (q q')

/-- Witness-killer for admissible summaries. -/
theorem witness_no_factor {P : Type u} [HistoryGraph P] {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
  {Q : Type uQ} (q : Summary (P := P) Q)
  (_h_adm : AdmissibleSummary q)
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

/--
Global non-reduction statement:
"For all ADMISSIBLE summaries q, holonomy does not factor through q."
This prevents trivial counterexamples where q encodes the path itself.
-/
def NonReducibleHolonomy {P : Type u} [HistoryGraph P] {S V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (Q : Type uQ) (q : Summary (P := P) Q),
    AdmissibleSummary q →
    ¬ FactorsHolonomy sem obs target_obs q

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.NonReducibleHolonomy

namespace PrimitiveHolonomy

/-
EXEMPLE CANONIQUE :
- Path = List Op (totals/schedulings)
- Deformation = refl ou swap local ab ↔ ba
- S = Nat × Bool, obs = fst, fibre(h) = { (h, b) }
- A toggles le bit seulement si y = 0 ; B fait juste avancer y.
- Témoin : αswap : ab ⇒ ba vs αrefl : ab ⇒ ab
  Hol(αswap) relie (0,false) à (0,true), mais Hol(αrefl) ne le fait pas.
  Donc non-factorisation par tout résumé 1D admissible.
-/

inductive Op where | A | B
deriving DecidableEq

open Op

/-- Histoires: objets = Nat, paths = listes d'opérations, 2-cellules = refl + swap ab↔ba. -/
instance : HistoryGraph Nat where
  Path _ _ := List Op
  Deformation := fun {h k} p q =>
      p = q
    ∨ (p = [A,B] ∧ q = [B,A])
    ∨ (p = [B,A] ∧ q = [A,B])
  idPath _ := []
  compPath p q := p ++ q

/-- Micro-dynamique (non-inversible OK car on l'encode en Relation via une fonction). -/
def step : Op → (Nat × Bool) → (Nat × Bool)
| A, (y,b) => (y+1, if y = 0 then (!b) else b)
| B, (y,b) => (y+1, b)

def run : List Op → (Nat × Bool) → (Nat × Bool)
| [],      s => s
| o :: os, s => run os (step o s)

/-- Sémantique relationnelle associée à run. obj = univ (on laisse Fiber faire le filtrage). -/

lemma run_append (p q : List Op) (s : Nat × Bool) : run (p ++ q) s = run q (run p s) := by
  induction p generalizing s with
  | nil => simp [run]
  | cons o os ih => simp [run, ih]

def exSem : Semantics Nat (Nat × Bool) :=
{ obj := fun _ => Set.univ
, sem := fun {h k} (p : HistoryGraph.Path h k) =>
    fun x y => y = run p x
, sem_dom := by
    intro h k p x y hxy
    -- obj = univ, trivial
    exact ⟨trivial, trivial⟩
, sem_id := by
    intro h
    funext x y
    -- sem [] x y ↔ y = x
    simp [relId, run]
    exact eq_comm
, sem_comp := by
    intro h k l p q
    funext x y
    -- y = run (p++q) x ↔ ∃z, z = run p x ∧ y = run q z
    -- donc ↔ relComp (sem p) (sem q) x y
    apply propext
    constructor
    · intro hy
      refine ⟨run p x, ?_, ?_⟩
      · exact rfl
      · change y = run q (run p x)
        rw [←run_append]
        exact hy
    · rintro ⟨z, hz1, hz2⟩
      change z = run p x at hz1
      change y = run q z at hz2
      rw [hz1] at hz2
      rw [←run_append] at hz2
      exact hz2
}

/-- Observable inertielle (le shadow 1D) : on ne voit que y. -/
def exObs : (Nat × Bool) → Nat := Prod.fst
def exTarget : Nat → Nat := fun h => h

/-- Deux totals et deux 2-cellules (swap vs refl). -/
def pAB : HistoryGraph.Path 0 2 := [A,B]
def pBA : HistoryGraph.Path 0 2 := [B,A]

def αswap : HistoryGraph.Deformation (h:=0) (k:=2) pAB pBA :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

def αrefl : HistoryGraph.Deformation (h:=0) (k:=2) pAB pAB :=
  Or.inl rfl

/-- Témoin (x,x') sur la fibre de départ 0. -/
def x  : (Nat × Bool) := (0, false)
def x' : (Nat × Bool) := (0, true)

/-- Hol(αswap) relie x à x'. -/
lemma hol_swap_holds :
  HolonomyRel exSem exObs exTarget (h:=0) (k:=2) (p:=pAB) (q:=pBA) αswap x x' :=
by
  -- via holonomy_def : ∃y, Transport pAB x y ∧ Transport pBA x' y
  -- on prend y = (2,true)
  refine (holonomy_def (sem:=exSem) (obs:=exObs) (target_obs:=exTarget)
          (h:=0) (k:=2) (p:=pAB) (q:=pBA) (α:=αswap) x x').2 ?_
  refine ⟨(2,true), ?_, ?_⟩
  · -- Transport pAB x (2,true)
    -- sem : y = run [A,B] x
    -- fibres: fst x = 0, fst y = 2
    dsimp [Transport, Fiber, exObs, exTarget, pAB, x, exSem, Relation]  -- unfold
    -- simp calcule run
    simp [run, step]
  · -- Transport pBA x' (2,true)
    dsimp [Transport, Fiber, exObs, exTarget, pBA, x', exSem, Relation]
    simp [run, step]

/-- Hol(αrefl) ne relie PAS x à x'. -/
lemma hol_refl_fails :
  ¬ HolonomyRel exSem exObs exTarget (h:=0) (k:=2) (p:=pAB) (q:=pAB) αrefl x x' :=
by
  intro hhol
  -- holonomy_def donne ∃y, Transport pAB x y ∧ Transport pAB x' y
  rcases (holonomy_def (sem:=exSem) (obs:=exObs) (target_obs:=exTarget)
          (h:=0) (k:=2) (p:=pAB) (q:=pAB) (α:=αrefl) x x').1 hhol with ⟨y, hy1, hy2⟩
  dsimp [Transport, Fiber, exSem] at hy1 hy2
  simp [run, step, pAB, x, x'] at hy1 hy2
  rw [hy1.1] at hy2
  simp at hy2

/-- Donc les deux holonomies sont différentes (témoin (x,x')). -/
lemma holonomies_different :
  HolonomyRel exSem exObs exTarget (h:=0) (k:=2) (p:=pAB) (q:=pBA) αswap
    ≠
  HolonomyRel exSem exObs exTarget (h:=0) (k:=2) (p:=pAB) (q:=pAB) αrefl :=
by
  intro hEq
  have : HolonomyRel exSem exObs exTarget (h:=0) (k:=2) (p:=pAB) (q:=pAB) αrefl x x' := by
    simpa [hEq] using hol_swap_holds
  exact hol_refl_fails this

/-- NON-REDUCTION (version opérationnelle) :
pour tout résumé 1D admissible q (invariant sous Deformation),
holonomie ne factorise pas par q. -/
theorem no_factor_for_any_admissible
  {Q : Type} (q : Summary (P:=Nat) Q) (hqadm : AdmissibleSummary (P:=Nat) q) :
  ¬ FactorsHolonomy (P:=Nat) (sem:=exSem) (obs:=exObs) (target_obs:=exTarget) q :=
by
  -- On applique witness_no_factor avec :
  -- α₁ = αswap (ab⇒ba), α₂ = αrefl (ab⇒ab),
  -- hp = rfl, hq = q(ba)=q(ab) (car Deformation ba ab), hne = holonomies_different.
  have hq : q pBA = q pAB := by
    -- Deformation pBA pAB est vraie (swap inverse)
    have : HistoryGraph.Deformation (h:=0) (k:=2) pBA pAB :=
      Or.inr (Or.inr ⟨rfl, rfl⟩)
    exact hqadm this
  -- hp : q pAB = q pAB
  have hp : q pAB = q pAB := rfl
  -- utilise ton witness_no_factor (celui déjà défini dans ton fichier)
  exact witness_no_factor (P:=Nat) (sem:=exSem) (obs:=exObs) (target_obs:=exTarget)
        (q:=q) (_h_adm:=hqadm) (p₁:=pAB) (q₁:=pBA) (α₁:=αswap)
        (p₂:=pAB) (q₂:=pAB) (α₂:=αrefl)
        hp hq holonomies_different

end PrimitiveHolonomy

#print axioms PrimitiveHolonomy.witness_no_factor
#print axioms PrimitiveHolonomy.NonReducibleHolonomy
#print axioms PrimitiveHolonomy.no_factor_for_any_admissible
