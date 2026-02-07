import RevHalt.Theory.PrimitiveHolonomy

/-!
# PrimitiveHolonomy × PA (fragment arithmétique minimal)

Objectif: repartir “de zéro” avec une dynamique arithmétique concrète (sans encoder toute la syntaxe de PA),
mais déjà assez structurée pour exhiber:

- une paire de chemins parallèles `p,q : h ⟶ k` (normalisations différentes vers la même forme normale),
- une 2-cellule admissible `p ⇒ q`,
- un `LagEvent` (un futur `step` qui discrimine deux micro-états dans la même fibre),
- et donc (via la théorie) un witness automatique contre toute stratégie qui ne dépend que de `obs`.

Tout est strictement constructif (pas de `classical`, pas de `noncomputable`).
-/

namespace PrimitiveHolonomy

namespace PAFragment

/-! ## 1) Termes arithmétiques (mini-fragment) -/

inductive Term : Type
  | zero : Term
  | succ : Term → Term
  | add  : Term → Term → Term
  deriving DecidableEq, Repr

def num : Nat → Term
  | 0     => Term.zero
  | n + 1 => Term.succ (num n)

def eval : Term → Nat
  | Term.zero     => 0
  | Term.succ t   => eval t + 1
  | Term.add a b  => eval a + eval b

def nf (t : Term) : Term := num (eval t)

/-! ## 2) Graphe d’histoires: deux normalisations parallèles + un pas futur -/

inductive APath : Term → Term → Type
  | id   (t : Term) : APath t t
  | p    (t : Term) : APath t (nf t)      -- “normalisation 1”
  | q    (t : Term) : APath t (nf t)      -- “normalisation 2”
  | step (t : Term) : APath t t           -- futur: discrimine le caché
  | comp {a b c : Term} : APath a b → APath b c → APath a c

inductive ADef : {h k : Term} → APath h k → APath h k → Prop
  | pq (t : Term) : ADef (APath.p t) (APath.q t)

instance : HistoryGraph Term where
  Path := APath
  Deformation := ADef
  idPath := APath.id
  compPath := APath.comp

/-!
## 3) Micro-états, observable, sémantique relationnelle

Ce fichier donne **deux** instanciations concrètes de `Semantics` sur le même graphe d’histoires:

1. `semantics` (aliasing pur): `R_p = R_q` et chaque sortie `y` a plusieurs antécédents `x`
   (relation non left-unique). On obtient alors une holonomie non-triviale de la forme `R ∘ R†`.
   Remarque: ici `p`/`q` restent **fonctionnels** (un seul `y` par `x`), mais ils oublient `hidden`,
   donc ils sont many-to-one.
2. `semantics_det` (mismatch de chemins): `R_p ≠ R_q`, et chacun est fonctionnel *et* left-unique
   (sur les fibres considérées).
   L’holonomie vient alors du **croisement** entre deux mises à jour différentes.
-/

abbrev State := LagState Term Bool

abbrev obs : State → Term := lagObs

def target_obs : Term → Term := fun t => t

/-!
### Un petit prédicat utilitaire (pour expliciter "aliasing" vs "déterminisme")

`LeftUniqueRel R` signifie: un point cible `y` ne peut pas avoir deux antécédents distincts
via `R` (sur le domaine donné).
-/

def LeftUniqueRel {A : Type} {B : Type} (R : Relation A B) : Prop :=
  ∀ ⦃x x' : A⦄ ⦃y : B⦄, R x y → R x' y → x = x'

/-!
`RightUniqueRel R` signifie: un point source `x` ne peut pas avoir deux images distinctes
via `R` (i.e. relation fonctionnelle, au sens “un seul `y` par `x`”).

`TotalRel R` signifie: chaque `x` a au moins une image (pas de blocage).
-/

def RightUniqueRel {A : Type} {B : Type} (R : Relation A B) : Prop :=
  ∀ ⦃x : A⦄ ⦃y y' : B⦄, R x y → R x y' → y = y'

def TotalRel {A : Type} {B : Type} (R : Relation A B) : Prop :=
  ∀ x : A, ∃ y : B, R x y

def FunctionalRel {A : Type} {B : Type} (R : Relation A B) : Prop :=
  TotalRel R ∧ RightUniqueRel R

/-- (Scenario 1) Transport `p`: écrase `hidden` à `false` et oublie le `hidden` d’entrée (aliasing). -/
def R_p (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = false

/-- (Scenario 1) Transport `q`: identique à `p` (aliasing pur, aucune différence de chemin). -/
def R_q (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = false

/-- Futur: ne garde compatibles que les états avec `hidden = false`. -/
def R_step (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = t ∧ a.hidden = false ∧ b.hidden = false

def sem : {h k : Term} → APath h k → Relation State State
  | _, _, APath.id _ => relId
  | _, _, APath.p t => R_p t
  | _, _, APath.q t => R_q t
  | _, _, APath.step t => R_step t
  | _, _, APath.comp u v => relComp (sem u) (sem v)

theorem sem_id (h : Term) : RelEq (sem (HistoryGraph.idPath h)) relId := by
  intro x y
  exact Iff.rfl

theorem sem_comp {h k l : Term} (path1 : HistoryGraph.Path h k) (path2 : HistoryGraph.Path k l) :
    RelEq (sem (HistoryGraph.compPath path1 path2)) (relComp (sem path1) (sem path2)) := by
  intro x y
  exact Iff.rfl

def semantics : Semantics Term State where
  sem := sem
  sem_id := sem_id
  sem_comp := sem_comp

/-! ## 4) Un witness explicite de TwistedHolonomy + LagEvent -/

def h0 : Term := Term.add (Term.succ Term.zero) (Term.succ Term.zero)

def x : FiberPt (P := Term) obs target_obs h0 :=
  ⟨⟨h0, false⟩, rfl⟩

def x' : FiberPt (P := Term) obs target_obs h0 :=
  ⟨⟨h0, true⟩, rfl⟩

theorem x_ne_x' : x ≠ x' := by
  intro h
  have : (x.1 : State) = x'.1 := congrArg Subtype.val h
  have : false = true := congrArg LagState.hidden this
  exact Bool.noConfusion this

def k0 : Term := nf h0

def y : FiberPt (P := Term) obs target_obs k0 :=
  ⟨⟨k0, false⟩, rfl⟩

def α : ADef (APath.p h0) (APath.q h0) := ADef.pq h0

theorem transport_p_x_y :
    Transport (P := Term) semantics obs target_obs (APath.p h0) x y := by
  show R_p h0 x.1 y.1
  exact ⟨rfl, rfl, rfl⟩

theorem transport_p_x'_y :
    Transport (P := Term) semantics obs target_obs (APath.p h0) x' y := by
  show R_p h0 x'.1 y.1
  exact ⟨rfl, rfl, rfl⟩

theorem transport_p_not_leftUnique :
    ¬ LeftUniqueRel (Transport (P := Term) semantics obs target_obs (APath.p h0)) := by
  intro hLU
  have : x = x' := hLU transport_p_x_y transport_p_x'_y
  exact x_ne_x' this

theorem transport_p_functional :
    FunctionalRel (Transport (P := Term) semantics obs target_obs (APath.p h0)) := by
  refine ⟨?total, ?ru⟩
  · intro x0
    rcases x0 with ⟨s0, hs0⟩
    refine ⟨y, ?_⟩
    -- `hs0` is exactly the fiber equation, unfolded without simp-magic.
    have hx0 : s0.visible = h0 := by
      dsimp [Fiber] at hs0
      simpa [obs, lagObs, target_obs] using hs0
    show R_p h0 s0 y.1
    exact ⟨hx0, rfl, rfl⟩
  · intro x0 y1 y2 hy1 hy2
    rcases y1 with ⟨s1, hs1⟩
    rcases y2 with ⟨s2, hs2⟩
    apply Subtype.ext
    cases s1 with
    | mk vis1 hid1 =>
      cases s2 with
      | mk vis2 hid2 =>
        have hy1' : R_p h0 x0.1 ⟨vis1, hid1⟩ := by
          simpa [Transport, semantics, sem, R_p] using hy1
        have hy2' : R_p h0 x0.1 ⟨vis2, hid2⟩ := by
          simpa [Transport, semantics, sem, R_p] using hy2
        have hvis : vis1 = vis2 := by
          -- both targets have visible = `nf h0`
          exact (hy1'.2.1).trans (hy2'.2.1).symm
        have hhid : hid1 = hid2 := by
          -- both targets have hidden = `false`
          exact (hy1'.2.2).trans (hy2'.2.2).symm
        cases hvis
        cases hhid
        rfl

theorem transport_q_x'_y :
    Transport (P := Term) semantics obs target_obs (APath.q h0) x' y := by
  show R_q h0 x'.1 y.1
  exact ⟨rfl, rfl, rfl⟩

theorem transport_q_x_y :
    Transport (P := Term) semantics obs target_obs (APath.q h0) x y := by
  show R_q h0 x.1 y.1
  exact ⟨rfl, rfl, rfl⟩

theorem transport_q_not_leftUnique :
    ¬ LeftUniqueRel (Transport (P := Term) semantics obs target_obs (APath.q h0)) := by
  intro hLU
  have : x = x' := hLU transport_q_x_y transport_q_x'_y
  exact x_ne_x' this

theorem transport_q_functional :
    FunctionalRel (Transport (P := Term) semantics obs target_obs (APath.q h0)) := by
  -- same relation as for `p`
  refine ⟨?total, ?ru⟩
  · intro x0
    rcases x0 with ⟨s0, hs0⟩
    refine ⟨y, ?_⟩
    have hx0 : s0.visible = h0 := by
      dsimp [Fiber] at hs0
      simpa [obs, lagObs, target_obs] using hs0
    show R_q h0 s0 y.1
    exact ⟨hx0, rfl, rfl⟩
  · intro x0 y1 y2 hy1 hy2
    rcases y1 with ⟨s1, hs1⟩
    rcases y2 with ⟨s2, hs2⟩
    apply Subtype.ext
    cases s1 with
    | mk vis1 hid1 =>
      cases s2 with
      | mk vis2 hid2 =>
        have hy1' : R_q h0 x0.1 ⟨vis1, hid1⟩ := by
          simpa [Transport, semantics, sem, R_q] using hy1
        have hy2' : R_q h0 x0.1 ⟨vis2, hid2⟩ := by
          simpa [Transport, semantics, sem, R_q] using hy2
        have hvis : vis1 = vis2 := (hy1'.2.1).trans (hy2'.2.1).symm
        have hhid : hid1 = hid2 := (hy1'.2.2).trans (hy2'.2.2).symm
        cases hvis
        cases hhid
        rfl

theorem holonomy_x_x' :
    HolonomyRel (P := Term) semantics obs target_obs α x x' := by
  refine ⟨y, transport_p_x_y, ?_⟩
  -- converse: Transport q x' y
  exact transport_q_x'_y

theorem twisted_holonomy :
    TwistedHolonomy (P := Term) semantics obs target_obs α := by
  exact ⟨x, x', x_ne_x', holonomy_x_x'⟩

theorem compatible_step_x :
    Compatible (P := Term) semantics obs target_obs (APath.step h0) x := by
  refine ⟨x, ?_⟩
  show R_step h0 x.1 x.1
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem not_compatible_step_x' :
    ¬ Compatible (P := Term) semantics obs target_obs (APath.step h0) x' := by
  intro hC
  rcases hC with ⟨z, hz⟩
  -- `R_step` forces source hidden = false, contradiction since `x'` has hidden = true.
  have hx'false : (x'.1.hidden = false) := (hz.2.2.1)  -- a.hidden = false
  have hx'true : (x'.1.hidden = true) := by simp [x']
  have : true = false := hx'true.symm.trans hx'false
  exact Bool.noConfusion this

theorem lag_event :
    LagEvent (P := Term) semantics obs target_obs α (APath.step h0) :=
  lag_of_witness (P := Term) semantics obs target_obs α (APath.step h0) x x'
    x_ne_x' holonomy_x_x' ⟨compatible_step_x, not_compatible_step_x'⟩

/-!
## 5) Corollaire “positif”: un `LagEvent` produit le witness qui force l’ajout d’une feature.

Ici on ne parle même pas de "prouver impossible": on obtient mécaniquement un couple `x,x'`
indiscernable par toute stratégie `σ = f ∘ obs`, mais séparé par un futur `step`.
-/

theorem lag_forces_feature
    {Q : Type uQ} (σ : FiberPt (P := Term) obs target_obs h0 → Q)
    (hσ : ∃ f : Term → Q, ∀ s, σ s = f (obs s.1)) :
    ∃ a b : FiberPt (P := Term) obs target_obs h0,
      σ a = σ b ∧
      Compatible (P := Term) semantics obs target_obs (APath.step h0) a ∧
      ¬ Compatible (P := Term) semantics obs target_obs (APath.step h0) b :=
by
  exact lagEvent_gives_summary_witness (P := Term) semantics obs target_obs α (APath.step h0) σ hσ lag_event

/-!
## 6) Second scénario: holonomie par mismatch de chemins (sans aliasing)

Ici on force le contraste avec le scénario 1.

On définit `p` et `q` comme deux **fonctions** (relations déterministes) sur les micro-états:

- `p` conserve `hidden`.
- `q` inverse `hidden`.

Les deux envoient `visible = t` vers `visible = nf t`.

Ainsi, il n’y a plus d’aliasing interne (pas de multi-antécédents pour un même `y`), mais l’holonomie
reste non-triviale parce que `p` et `q` ne “recollent” pas les fibres de la même façon.
-/

/-- (Scenario 2) `p` est déterministe: `hidden` est transporté tel quel. -/
def R_p_det (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = a.hidden

/-- (Scenario 2) `q` est déterministe: `hidden` est inversé. -/
def R_q_det (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = !a.hidden

def sem_det : {h k : Term} → APath h k → Relation State State
  | _, _, APath.id _ => relId
  | _, _, APath.p t => R_p_det t
  | _, _, APath.q t => R_q_det t
  | _, _, APath.step t => R_step t
  | _, _, APath.comp u v => relComp (sem_det u) (sem_det v)

theorem sem_det_id (h : Term) : RelEq (sem_det (HistoryGraph.idPath h)) relId := by
  intro x y
  exact Iff.rfl

theorem sem_det_comp {h k l : Term} (path1 : HistoryGraph.Path h k) (path2 : HistoryGraph.Path k l) :
    RelEq (sem_det (HistoryGraph.compPath path1 path2)) (relComp (sem_det path1) (sem_det path2)) := by
  intro x y
  exact Iff.rfl

def semantics_det : Semantics Term State where
  sem := sem_det
  sem_id := sem_det_id
  sem_comp := sem_det_comp

def xd : FiberPt (P := Term) obs target_obs h0 :=
  ⟨⟨h0, false⟩, rfl⟩

def x'd : FiberPt (P := Term) obs target_obs h0 :=
  ⟨⟨h0, true⟩, rfl⟩

theorem xd_ne_x'd : xd ≠ x'd := by
  intro h
  have : (xd.1 : State) = x'd.1 := congrArg Subtype.val h
  have : false = true := congrArg LagState.hidden this
  exact Bool.noConfusion this

def yd : FiberPt (P := Term) obs target_obs k0 :=
  ⟨⟨k0, false⟩, rfl⟩

theorem transport_p_det_xd_yd :
    Transport (P := Term) semantics_det obs target_obs (APath.p h0) xd yd := by
  show R_p_det h0 xd.1 yd.1
  -- visible = h0, visible = nf h0, hidden preserved (false -> false)
  exact ⟨rfl, rfl, rfl⟩

theorem transport_q_det_x'd_yd :
    Transport (P := Term) semantics_det obs target_obs (APath.q h0) x'd yd := by
  show R_q_det h0 x'd.1 yd.1
  -- visible = h0, visible = nf h0, hidden toggled (true -> false)
  refine ⟨rfl, rfl, ?_⟩
  simp [x'd, yd]

theorem transport_p_det_leftUnique :
    LeftUniqueRel (Transport (P := Term) semantics_det obs target_obs (APath.p h0)) := by
  intro x1 x2 y1 h1 h2
  rcases x1 with ⟨s1, hs1⟩
  rcases x2 with ⟨s2, hs2⟩
  apply Subtype.ext
  cases s1 with
  | mk vis1 hid1 =>
    cases s2 with
    | mk vis2 hid2 =>
      have hvis : vis1 = vis2 := by
        -- membership in the same fiber over `h0`
        simpa [obs, lagObs, target_obs] using (hs1.trans hs2.symm)
      have h1' : R_p_det h0 ⟨vis1, hid1⟩ (y1.1) := by
        simpa [Transport, semantics_det, sem_det, R_p_det] using h1
      have h2' : R_p_det h0 ⟨vis2, hid2⟩ (y1.1) := by
        simpa [Transport, semantics_det, sem_det, R_p_det] using h2
      have hhid : hid1 = hid2 := by
        -- both say `y1.hidden` equals the source `hidden`
        have hy1 : (y1.1.hidden = hid1) := h1'.2.2
        have hy2 : (y1.1.hidden = hid2) := h2'.2.2
        -- rewrite `vis2` to `vis1` is irrelevant here; only `hidden` matters.
        exact hy1.symm.trans (by simpa [hvis] using hy2)
      cases hvis
      cases hhid
      rfl

theorem transport_p_det_functional :
    FunctionalRel (Transport (P := Term) semantics_det obs target_obs (APath.p h0)) := by
  refine ⟨?total, ?ru⟩
  · intro x0
    rcases x0 with ⟨s0, hs0⟩
    -- the unique target keeps the same hidden bit
    refine ⟨⟨⟨k0, s0.hidden⟩, rfl⟩, ?_⟩
    have hx0 : s0.visible = h0 := by
      dsimp [Fiber] at hs0
      simpa [obs, lagObs, target_obs] using hs0
    show R_p_det h0 s0 ⟨k0, s0.hidden⟩
    exact ⟨hx0, rfl, rfl⟩
  · intro x0 y1 y2 hy1 hy2
    rcases y1 with ⟨s1, hs1⟩
    rcases y2 with ⟨s2, hs2⟩
    apply Subtype.ext
    cases s1 with
    | mk vis1 hid1 =>
      cases s2 with
      | mk vis2 hid2 =>
        have hy1' : R_p_det h0 x0.1 ⟨vis1, hid1⟩ := by
          simpa [Transport, semantics_det, sem_det, R_p_det] using hy1
        have hy2' : R_p_det h0 x0.1 ⟨vis2, hid2⟩ := by
          simpa [Transport, semantics_det, sem_det, R_p_det] using hy2
        have hvis : vis1 = vis2 := (hy1'.2.1).trans (hy2'.2.1).symm
        have hhid : hid1 = hid2 := by
          -- both equal `x0.hidden`
          have hh1 : hid1 = x0.1.hidden := by simpa using hy1'.2.2
          have hh2 : hid2 = x0.1.hidden := by simpa using hy2'.2.2
          exact hh1.trans hh2.symm
        cases hvis
        cases hhid
        rfl

theorem transport_q_det_leftUnique :
    LeftUniqueRel (Transport (P := Term) semantics_det obs target_obs (APath.q h0)) := by
  intro x1 x2 y1 h1 h2
  rcases x1 with ⟨s1, hs1⟩
  rcases x2 with ⟨s2, hs2⟩
  apply Subtype.ext
  cases s1 with
  | mk vis1 hid1 =>
    cases s2 with
    | mk vis2 hid2 =>
      have hvis : vis1 = vis2 := by
        simpa [obs, lagObs, target_obs] using (hs1.trans hs2.symm)
      have h1' : R_q_det h0 ⟨vis1, hid1⟩ (y1.1) := by
        simpa [Transport, semantics_det, sem_det, R_q_det] using h1
      have h2' : R_q_det h0 ⟨vis2, hid2⟩ (y1.1) := by
        simpa [Transport, semantics_det, sem_det, R_q_det] using h2
      have hhid : hid1 = hid2 := by
        have hy1 : (y1.1.hidden = !hid1) := h1'.2.2
        have hy2 : (y1.1.hidden = !hid2) := h2'.2.2
        have hnot : (!hid1) = (!hid2) := hy1.symm.trans hy2
        -- `Bool.not` est involutif, donc injectif: `!hid1 = !hid2` implique `hid1 = hid2`.
        simpa using (congrArg (fun b => !b) hnot)
      cases hvis
      cases hhid
      rfl

theorem transport_q_det_functional :
    FunctionalRel (Transport (P := Term) semantics_det obs target_obs (APath.q h0)) := by
  refine ⟨?total, ?ru⟩
  · intro x0
    rcases x0 with ⟨s0, hs0⟩
    -- the unique target flips the hidden bit
    refine ⟨⟨⟨k0, !s0.hidden⟩, rfl⟩, ?_⟩
    have hx0 : s0.visible = h0 := by
      dsimp [Fiber] at hs0
      simpa [obs, lagObs, target_obs] using hs0
    show R_q_det h0 s0 ⟨k0, !s0.hidden⟩
    exact ⟨hx0, rfl, rfl⟩
  · intro x0 y1 y2 hy1 hy2
    rcases y1 with ⟨s1, hs1⟩
    rcases y2 with ⟨s2, hs2⟩
    apply Subtype.ext
    cases s1 with
    | mk vis1 hid1 =>
      cases s2 with
      | mk vis2 hid2 =>
        have hy1' : R_q_det h0 x0.1 ⟨vis1, hid1⟩ := by
          simpa [Transport, semantics_det, sem_det, R_q_det] using hy1
        have hy2' : R_q_det h0 x0.1 ⟨vis2, hid2⟩ := by
          simpa [Transport, semantics_det, sem_det, R_q_det] using hy2
        have hvis : vis1 = vis2 := (hy1'.2.1).trans (hy2'.2.1).symm
        have hhid : hid1 = hid2 := by
          have hh1 : hid1 = !x0.1.hidden := by simpa using hy1'.2.2
          have hh2 : hid2 = !x0.1.hidden := by simpa using hy2'.2.2
          exact hh1.trans hh2.symm
        cases hvis
        cases hhid
        rfl

theorem holonomy_det_xd_x'd :
    HolonomyRel (P := Term) semantics_det obs target_obs α xd x'd := by
  refine ⟨yd, transport_p_det_xd_yd, ?_⟩
  exact transport_q_det_x'd_yd

theorem twisted_holonomy_det :
    TwistedHolonomy (P := Term) semantics_det obs target_obs α := by
  exact ⟨xd, x'd, xd_ne_x'd, holonomy_det_xd_x'd⟩

theorem compatible_step_xd :
    Compatible (P := Term) semantics_det obs target_obs (APath.step h0) xd := by
  refine ⟨xd, ?_⟩
  show R_step h0 xd.1 xd.1
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem not_compatible_step_x'd :
    ¬ Compatible (P := Term) semantics_det obs target_obs (APath.step h0) x'd := by
  intro hC
  rcases hC with ⟨z, hz⟩
  have hx'false : (x'd.1.hidden = false) := (hz.2.2.1)
  have hx'true : (x'd.1.hidden = true) := by simp [x'd]
  have : true = false := hx'true.symm.trans hx'false
  exact Bool.noConfusion this

theorem lag_event_det :
    LagEvent (P := Term) semantics_det obs target_obs α (APath.step h0) :=
  lag_of_witness (P := Term) semantics_det obs target_obs α (APath.step h0) xd x'd
    xd_ne_x'd holonomy_det_xd_x'd ⟨compatible_step_xd, not_compatible_step_x'd⟩

theorem lag_forces_feature_det
    {Q : Type uQ} (σ : FiberPt (P := Term) obs target_obs h0 → Q)
    (hσ : ∃ f : Term → Q, ∀ s, σ s = f (obs s.1)) :
    ∃ a b : FiberPt (P := Term) obs target_obs h0,
      σ a = σ b ∧
      Compatible (P := Term) semantics_det obs target_obs (APath.step h0) a ∧
      ¬ Compatible (P := Term) semantics_det obs target_obs (APath.step h0) b :=
by
  exact lagEvent_gives_summary_witness (P := Term) semantics_det obs target_obs α (APath.step h0) σ hσ lag_event_det

end PAFragment

end PrimitiveHolonomy
