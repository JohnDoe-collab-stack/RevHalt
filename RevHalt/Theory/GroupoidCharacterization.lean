/-!
# Groupoïde = Base réversible + Holonomie plate sur les unités

Formalization of the groupoid characterization theorem:
  **(C1) + (C2) ⟺ groupoid structure on fibers**

where:
- C1 = homotopy reversibility of the base
- C2 = flat holonomy on unit 2-cells

Strictly constructive (no `noncomputable`, no `classical`).
Self-contained — no imports beyond Lean core.
-/

universe u v w

namespace GrpChar

/-! ## Relation primitives -/

@[reducible] def Rel (A : Type u) (B : Type v) := A → B → Prop

def RelEq {A : Type u} {B : Type v} (R S : Rel A B) : Prop :=
  ∀ x y, R x y ↔ S x y

@[reducible] def relComp {A : Type u} {B : Type v} {C : Type w}
    (R : Rel A B) (S : Rel B C) : Rel A C :=
  fun a c ↦ ∃ b, R a b ∧ S b c

@[reducible] def relId {A : Type u} : Rel A A := fun x y ↦ x = y

@[reducible] def relConv {A : Type u} {B : Type v} (R : Rel A B) : Rel B A :=
  fun b a ↦ R a b

/-! ## 2-Category, Semantics, Fibers -/

class HG (P : Type u) where
  Path : P → P → Type v
  Def : {h k : P} → Path h k → Path h k → Prop
  idP (h : P) : Path h h
  comp {h k l : P} : Path h k → Path k l → Path h l

structure Sem (P : Type u) [HG P] (S : Type w) where
  sem : {h k : P} → HG.Path h k → Rel S S
  sem_id : ∀ h, RelEq (sem (HG.idP h)) relId
  sem_comp : ∀ {h k l} (p : HG.Path h k) (q : HG.Path k l),
    RelEq (sem (HG.comp p q)) (relComp (sem p) (sem q))

def FibPt {P : Type u} [HG P] {S V : Type w}
    (obs : S → V) (tgt : P → V) (h : P) : Type w :=
  { x : S // obs x = tgt h }

def Tr {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    {h k : P} (p : HG.Path h k) : Rel (FibPt obs tgt h) (FibPt obs tgt k) :=
  fun x y ↦ s.sem p x.1 y.1

def Hol {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    {h k : P} {p q : HG.Path h k} (_α : HG.Def p q) :
    Rel (FibPt obs tgt h) (FibPt obs tgt h) :=
  relComp (Tr s obs tgt p) (relConv (Tr s obs tgt q))

/-- Semantics preserves fibers. -/
def FibPres {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V) : Prop :=
  ∀ {h k : P} (p : HG.Path h k) (x y : S),
    obs x = tgt h → s.sem p x y → obs y = tgt k

/-! ================================================================
    ## THE KEY LEMMA IN Rel
    ================================================================ -/

/-- R ∘ S = Δ ∧ S ∘ R = Δ ⟹ R deterministic. -/
theorem rel_inv_det {X Y : Type w}
    (R : Rel X Y) (S : Rel Y X)
    (hRS : RelEq (relComp R S) (@relId X))
    (hSR : RelEq (relComp S R) (@relId Y)) :
    ∀ x y₁ y₂, R x y₁ → R x y₂ → y₁ = y₂ := by
  intro x y₁ y₂ hr1 hr2
  have hxx : relComp R S x x := (hRS x x).mpr rfl
  obtain ⟨y₀, hRy0, hSy0⟩ := hxx
  have h01 : y₀ = y₁ := (hSR y₀ y₁).mp ⟨x, hSy0, hr1⟩
  have h02 : y₀ = y₂ := (hSR y₀ y₂).mp ⟨x, hSy0, hr2⟩
  exact h01.symm.trans h02

/-- ⟹ total. -/
theorem rel_inv_tot {X Y : Type w}
    (R : Rel X Y) (S : Rel Y X)
    (hRS : RelEq (relComp R S) (@relId X)) :
    ∀ x, ∃ y, R x y := by
  intro x
  obtain ⟨y, hRy, _⟩ := (hRS x x).mpr rfl
  exact ⟨y, hRy⟩

/-- ⟹ injective. -/
theorem rel_inv_inj {X Y : Type w}
    (R : Rel X Y) (S : Rel Y X)
    (hRS : RelEq (relComp R S) (@relId X))
    (hSR : RelEq (relComp S R) (@relId Y)) :
    ∀ x₁ x₂ y, R x₁ y → R x₂ y → x₁ = x₂ := by
  have hSdet := rel_inv_det S R hSR hRS
  have hRdet := rel_inv_det R S hRS hSR
  intro x₁ x₂ y hr1 hr2
  obtain ⟨y₁, hRy1, hSy1⟩ := (hRS x₁ x₁).mpr rfl
  have h1 : y₁ = y := hRdet x₁ y₁ y hRy1 hr1
  obtain ⟨y₂, hRy2, hSy2⟩ := (hRS x₂ x₂).mpr rfl
  have h2 : y₂ = y := hRdet x₂ y₂ y hRy2 hr2
  exact hSdet y x₁ x₂ (h1 ▸ hSy1) (h2 ▸ hSy2)

/-- ⟹ surjective. -/
theorem rel_inv_surj {X Y : Type w}
    (R : Rel X Y) (S : Rel Y X)
    (hSR : RelEq (relComp S R) (@relId Y)) :
    ∀ y, ∃ x, R x y := by
  intro y
  obtain ⟨x, _, hRx⟩ := (hSR y y).mpr rfl
  exact ⟨x, hRx⟩

/-- ⟹ S = R†. -/
theorem rel_inv_conv {X Y : Type w}
    (R : Rel X Y) (S : Rel Y X)
    (hRS : RelEq (relComp R S) (@relId X))
    (hSR : RelEq (relComp S R) (@relId Y)) :
    RelEq S (relConv R) := by
  intro y x
  constructor
  · intro hSyx
    obtain ⟨y', hRxy'⟩ := rel_inv_tot R S hRS x
    have : y = y' := (hSR y y').mp ⟨x, hSyx, hRxy'⟩
    subst this; exact hRxy'
  · intro hRxy
    obtain ⟨x', hSyx'⟩ := rel_inv_tot S R hSR y
    have : x = x' := (hRS x x').mp ⟨y, hRxy, hSyx'⟩
    subst this; exact hSyx'

/-! ================================================================
    ## STRUCTURES: C1, C2, FiberGroupoid
    ================================================================ -/

structure HomotopyRev (P : Type u) [HG P] : Prop where
  rev : ∀ {h k : P} (p : HG.Path h k),
    ∃ (q : HG.Path k h)
      (_ : HG.Def (HG.comp p q) (HG.idP h))
      (_ : HG.Def (HG.comp q p) (HG.idP k)), True

structure FlatUnits {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V) : Prop where
  flat_η : ∀ {h k : P} (p : HG.Path h k) (q : HG.Path k h)
    (η : HG.Def (HG.comp p q) (HG.idP h)),
    RelEq (Hol s obs tgt η) relId
  flat_ε : ∀ {h k : P} (p : HG.Path h k) (q : HG.Path k h)
    (ε : HG.Def (HG.comp q p) (HG.idP k)),
    RelEq (Hol s obs tgt ε) relId

structure FibGrpd {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V) : Prop where
  tot : ∀ {h k : P} (p : HG.Path h k) (x : FibPt obs tgt h), ∃ y, Tr s obs tgt p x y
  det : ∀ {h k : P} (p : HG.Path h k) (x : FibPt obs tgt h) (y₁ y₂ : FibPt obs tgt k),
    Tr s obs tgt p x y₁ → Tr s obs tgt p x y₂ → y₁ = y₂
  inj : ∀ {h k : P} (p : HG.Path h k) (x₁ x₂ : FibPt obs tgt h) (y : FibPt obs tgt k),
    Tr s obs tgt p x₁ y → Tr s obs tgt p x₂ y → x₁ = x₂
  surj : ∀ {h k : P} (p : HG.Path h k) (y : FibPt obs tgt k), ∃ x, Tr s obs tgt p x y
  inv : ∀ {h k : P} (p : HG.Path h k),
    ∃ q : HG.Path k h, RelEq (Tr s obs tgt q) (relConv (Tr s obs tgt p))

/-! ================================================================
    ## TRANSPORT LEMMAS
    ================================================================ -/

theorem tr_comp {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (fp : FibPres s obs tgt)
    {h k l : P} (p : HG.Path h k) (q : HG.Path k l)
    (x : FibPt obs tgt h) (z : FibPt obs tgt l) :
    Tr s obs tgt (HG.comp p q) x z ↔
    ∃ y : FibPt obs tgt k, Tr s obs tgt p x y ∧ Tr s obs tgt q y z := by
  constructor
  · intro hT
    obtain ⟨m, hpm, hqm⟩ := (s.sem_comp p q x.1 z.1).mp hT
    exact ⟨⟨m, fp p x.1 m x.2 hpm⟩, hpm, hqm⟩
  · intro ⟨y, hpy, hqy⟩
    exact (s.sem_comp p q x.1 z.1).mpr ⟨y.1, hpy, hqy⟩

theorem tr_id {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (h : P) (x y : FibPt obs tgt h) :
    Tr s obs tgt (HG.idP h) x y ↔ x = y := by
  constructor
  · intro hT
    exact Subtype.ext ((s.sem_id h x.1 y.1).mp hT)
  · intro heq
    subst heq
    exact (s.sem_id h x.1 x.1).mpr rfl

/-- Hol(η) ↔ T_p ∘ T_q for η : comp(p,q) ⇒ id_h. -/
theorem hol_eta {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (fp : FibPres s obs tgt)
    {h k : P} (p : HG.Path h k) (q : HG.Path k h)
    (η : HG.Def (HG.comp p q) (HG.idP h))
    (x x' : FibPt obs tgt h) :
    Hol s obs tgt η x x' ↔ relComp (Tr s obs tgt p) (Tr s obs tgt q) x x' := by
  constructor
  · intro ⟨w, hTpq_xw, hTid_x'w⟩
    have : x' = w := (tr_id s obs tgt h x' w).mp hTid_x'w
    subst this
    obtain ⟨m, hpm, hqm⟩ := (tr_comp s obs tgt fp p q x x').mp hTpq_xw
    exact ⟨m, hpm, hqm⟩
  · intro ⟨m, hpm, hqm⟩
    exact ⟨x', (tr_comp s obs tgt fp p q x x').mpr ⟨m, hpm, hqm⟩,
           (tr_id s obs tgt h x' x').mpr rfl⟩

/-- Hol(ε) ↔ T_q ∘ T_p for ε : comp(q,p) ⇒ id_k. -/
theorem hol_eps {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (fp : FibPres s obs tgt)
    {h k : P} (p : HG.Path h k) (q : HG.Path k h)
    (ε : HG.Def (HG.comp q p) (HG.idP k))
    (y y' : FibPt obs tgt k) :
    Hol s obs tgt ε y y' ↔ relComp (Tr s obs tgt q) (Tr s obs tgt p) y y' := by
  constructor
  · intro ⟨w, hTqp_yw, hTid_y'w⟩
    have : y' = w := (tr_id s obs tgt k y' w).mp hTid_y'w
    subst this
    obtain ⟨m, hqm, hpm⟩ := (tr_comp s obs tgt fp q p y y').mp hTqp_yw
    exact ⟨m, hqm, hpm⟩
  · intro ⟨m, hqm, hpm⟩
    exact ⟨y', (tr_comp s obs tgt fp q p y y').mpr ⟨m, hqm, hpm⟩,
           (tr_id s obs tgt k y' y').mpr rfl⟩

/-! ================================================================
    ## FORWARD DIRECTION: C1 + C2 ⟹ FiberGroupoid
    ================================================================ -/

theorem fwd {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (fp : FibPres s obs tgt)
    (hC1 : HomotopyRev P)
    (hC2 : FlatUnits s obs tgt) :
    FibGrpd s obs tgt := by
  -- Helper: from C2 flat_η, derive T_p ∘ T_q = relId
  have mk_pq : ∀ {h k : P} (p : HG.Path h k) (q : HG.Path k h)
      (η : HG.Def (HG.comp p q) (HG.idP h)),
      RelEq (relComp (Tr s obs tgt p) (Tr s obs tgt q)) relId := by
    intro h k p q η a a'
    exact Iff.trans (hol_eta s obs tgt fp p q η a a').symm (hC2.flat_η p q η a a')
  -- Helper: from C2 flat_ε, derive T_q ∘ T_p = relId
  have mk_qp : ∀ {h k : P} (p : HG.Path h k) (q : HG.Path k h)
      (ε : HG.Def (HG.comp q p) (HG.idP k)),
      RelEq (relComp (Tr s obs tgt q) (Tr s obs tgt p)) relId := by
    intro h k p q ε a a'
    exact Iff.trans (hol_eps s obs tgt fp p q ε a a').symm (hC2.flat_ε p q ε a a')
  constructor
  · -- total
    intro h k p x
    obtain ⟨q, η, _, _⟩ := hC1.rev p
    exact rel_inv_tot (Tr s obs tgt p) (Tr s obs tgt q) (mk_pq p q η) x
  · -- det
    intro h k p x y₁ y₂ h1 h2
    obtain ⟨q, η, ε, _⟩ := hC1.rev p
    exact rel_inv_det (Tr s obs tgt p) (Tr s obs tgt q) (mk_pq p q η) (mk_qp p q ε) x y₁ y₂ h1 h2
  · -- inj
    intro h k p x₁ x₂ y h1 h2
    obtain ⟨q, η, ε, _⟩ := hC1.rev p
    exact rel_inv_inj (Tr s obs tgt p) (Tr s obs tgt q) (mk_pq p q η) (mk_qp p q ε) x₁ x₂ y h1 h2
  · -- surj
    intro h k p y
    obtain ⟨q, _, ε, _⟩ := hC1.rev p
    exact rel_inv_surj (Tr s obs tgt p) (Tr s obs tgt q) (mk_qp p q ε) y
  · -- inv
    intro h k p
    obtain ⟨q, η, ε, _⟩ := hC1.rev p
    exact ⟨q, rel_inv_conv (Tr s obs tgt p) (Tr s obs tgt q) (mk_pq p q η) (mk_qp p q ε)⟩

/-! ================================================================
    ## BACKWARD DIRECTION (C2 part): Groupoid ⟹ flat on specific units
    ================================================================ -/

theorem bwd_C2 {P : Type u} [HG P] {S V : Type w}
    (s : Sem P S) (obs : S → V) (tgt : P → V)
    (fp : FibPres s obs tgt)
    (g : FibGrpd s obs tgt)
    {h k : P} (p : HG.Path h k) (q : HG.Path k h)
    (hTq : RelEq (Tr s obs tgt q) (relConv (Tr s obs tgt p)))
    (η : HG.Def (HG.comp p q) (HG.idP h)) :
    RelEq (Hol s obs tgt η) relId := by
  intro x x'
  unfold Hol relComp relConv relId
  constructor
  · intro ⟨w, hTpq_xw, hTid_x'w⟩
    -- hTid_x'w : Tr s obs tgt (HG.idP h) x' w (the converse flips to this)
    have heq_x'w : x' = w := (tr_id s obs tgt h x' w).mp hTid_x'w
    subst heq_x'w
    obtain ⟨m_val, hpm, hqm⟩ := (s.sem_comp p q x.1 x'.1).mp hTpq_xw
    have hm_fib : obs m_val = tgt k := fp p x.1 m_val x.2 hpm
    have hTp_x'm : s.sem p x'.1 m_val := (hTq ⟨m_val, hm_fib⟩ x').mp hqm
    exact g.inj p x x' ⟨m_val, hm_fib⟩ hpm hTp_x'm
  · intro heq
    subst heq
    obtain ⟨m, hpm⟩ := g.tot p x
    have hqm : Tr s obs tgt q m x := (hTq m x).mpr hpm
    exact ⟨x, (s.sem_comp p q x.1 x.1).mpr ⟨m.1, hpm, hqm⟩,
           (tr_id s obs tgt h x x).mpr rfl⟩

end GrpChar

#print axioms GrpChar.rel_inv_det
#print axioms GrpChar.rel_inv_conv
#print axioms GrpChar.fwd
#print axioms GrpChar.bwd_C2
