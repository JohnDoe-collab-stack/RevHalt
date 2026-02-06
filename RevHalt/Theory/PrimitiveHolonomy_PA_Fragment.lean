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

/-! ## 3) Micro-états, observable, sémantique relationnelle -/

abbrev State := LagState Term Bool

abbrev obs : State → Term := lagObs

def target_obs : Term → Term := fun t => t

def R_p (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = false

def R_q (t : Term) : Relation State State :=
  fun a b => a.visible = t ∧ b.visible = nf t ∧ b.hidden = false

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

theorem transport_q_x'_y :
    Transport (P := Term) semantics obs target_obs (APath.q h0) x' y := by
  show R_q h0 x'.1 y.1
  exact ⟨rfl, rfl, rfl⟩

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

end PAFragment

end PrimitiveHolonomy
