import RevHalt.Theory.PrimitiveHolonomy

/-!
# PrimitiveHolonomy Instance: A Concrete Non-Trivial Model

This file provides a minimal but non-trivial instantiation of the
`PrimitiveHolonomy` framework with explicit witnesses for:
- `TwistedHolonomy`
- `LagEvent` (via `StepDependsOnHidden`)
- `¬ FactorsHolonomy`

All constructions are strictly constructive (no `classical`, no `noncomputable`).
-/

namespace PrimitiveHolonomy

/-! ## 1. Tiny HistoryGraph: ToyPath and ToyDef -/

/-- Minimal path language with parallel paths p, q, r and a step for lag. -/
inductive ToyPath : Unit → Unit → Type where
  | id   : ToyPath () ()
  | p    : ToyPath () ()  -- "interesting" path
  | q    : ToyPath () ()  -- second path, used for holonomy (p ⇒ q)
  | r    : ToyPath () ()  -- third path, used to force non-factorization (p ⇒ r)
  | step : ToyPath () ()  -- used for compatibility / lag
  | comp : ToyPath () () → ToyPath () () → ToyPath () ()

/-- Two generating 2-cells: p ⇒ q and p ⇒ r. -/
inductive ToyDef : {h k : Unit} → ToyPath h k → ToyPath h k → Prop where
  | pq : ToyDef ToyPath.p ToyPath.q
  | pr : ToyDef ToyPath.p ToyPath.r

/-- The HistoryGraph instance for Unit with ToyPath. -/
instance toyHistoryGraph : HistoryGraph Unit where
  Path := ToyPath
  Deformation := ToyDef
  idPath := fun _ => ToyPath.id
  compPath := ToyPath.comp

/-! ## 2. State Space and Observables -/

/-- State space: LagState with trivial visible part and Bool hidden part. -/
abbrev ToyState := LagState Unit Bool

/-- Observable projection. -/
abbrev toyObs : ToyState → Unit := lagObs

/-- Target observable (constant). -/
def toyTargetObs : Unit → Unit := fun _ => ()

/-- Base states. -/
def s0 : ToyState := ⟨(), false⟩
def s1 : ToyState := ⟨(), true⟩

/-- Fiber points. -/
def x : FiberPt (P := Unit) toyObs toyTargetObs () := ⟨s0, rfl⟩
def x' : FiberPt (P := Unit) toyObs toyTargetObs () := ⟨s1, rfl⟩

/-- x ≠ x' -/
theorem x_ne_x' : x ≠ x' := by
  intro h
  have : s0 = s1 := congrArg Subtype.val h
  have : false = true := congrArg LagState.hidden this
  exact Bool.noConfusion this

/-- Hidden components differ. -/
theorem hidden_ne : x.1.hidden ≠ x'.1.hidden := by
  intro h
  exact Bool.noConfusion h

/-! ## 3. Semantics -/

/-- Relation for path p: false → true. -/
def R_p : Relation ToyState ToyState :=
  fun a b => a.hidden = false ∧ b.hidden = true ∧ b.visible = ()

/-- Relation for path q: identity. -/
def R_q : Relation ToyState ToyState := relId

/-- Relation for path r: empty (used to separate holonomies). -/
def R_r : Relation ToyState ToyState := fun _ _ => False

/-- Relation for step: preserves hidden = false. -/
def R_step : Relation ToyState ToyState :=
  fun a b => a.hidden = false ∧ b.hidden = false ∧ b.visible = ()

/-- Semantic interpretation of paths. -/
def toySem : {h k : Unit} → ToyPath h k → Relation ToyState ToyState
  | _, _, ToyPath.id => relId
  | _, _, ToyPath.p => R_p
  | _, _, ToyPath.q => R_q
  | _, _, ToyPath.r => R_r
  | _, _, ToyPath.step => R_step
  | _, _, ToyPath.comp u v => relComp (toySem u) (toySem v)

/-- sem_id: identity path gives identity relation. -/
theorem toySem_id (h : Unit) : RelEq (toySem (HistoryGraph.idPath h)) relId := by
  intro x y
  exact Iff.rfl

/-- sem_comp: composition is definitional. -/
theorem toySem_comp {h k l : Unit} (path1 : HistoryGraph.Path h k) (path2 : HistoryGraph.Path k l) :
    RelEq (toySem (HistoryGraph.compPath path1 path2)) (relComp (toySem path1) (toySem path2)) := by
  intro x y
  exact Iff.rfl

/-- The Semantics structure. -/
def toySemantics : Semantics Unit ToyState where
  sem := toySem
  sem_id := toySem_id
  sem_comp := toySem_comp

/-! ## 4. Witness: TwistedHolonomy -/

/-- The 2-cell α₁ : p ⇒ q. -/
def α₁ : ToyDef ToyPath.p ToyPath.q := ToyDef.pq

/-- Transport via p from x to x'. -/
theorem transport_p_x_x' : Transport toySemantics toyObs toyTargetObs ToyPath.p x x' := by
  show R_p s0 s1
  exact ⟨rfl, rfl, rfl⟩

/-- Transport via q from x' to x' (identity). -/
theorem transport_q_x'_x' : Transport toySemantics toyObs toyTargetObs ToyPath.q x' x' := by
  show R_q s1 s1
  show s1 = s1
  rfl

/-- Holonomy relates x to x'. -/
theorem holonomy_x_x' : HolonomyRel toySemantics toyObs toyTargetObs α₁ x x' := by
  -- HolonomyRel = relComp (Transport p) (relConverse (Transport q))
  -- Need: ∃ y, Transport p x y ∧ Transport q x' y
  refine ⟨x', transport_p_x_x', ?_⟩
  exact transport_q_x'_x'

/-- Main witness: TwistedHolonomy. -/
theorem twisted_holonomy_witness :
    TwistedHolonomy toySemantics toyObs toyTargetObs α₁ :=
  ⟨x, x', x_ne_x', holonomy_x_x'⟩

/-! ## 5. Witness: LagEvent -/

/-- x is compatible with step (pick y := x). -/
theorem compatible_step_x : Compatible toySemantics toyObs toyTargetObs ToyPath.step x := by
  refine ⟨x, ?_⟩
  show R_step s0 s0
  exact ⟨rfl, rfl, rfl⟩

/-- StepDependsOnHidden for step path. -/
theorem step_depends_on_hidden :
    StepDependsOnHidden (P := Unit) toySemantics toyTargetObs ToyPath.step := by
  intro a b hHidden hBoth
  obtain ⟨hCompatA, hCompatB⟩ := hBoth
  -- From Compatible a, we get a.1.hidden = false
  obtain ⟨yA, hA⟩ := hCompatA
  have ha_false : a.1.hidden = false := hA.1
  -- From Compatible b, we get b.1.hidden = false
  obtain ⟨yB, hB⟩ := hCompatB
  have hb_false : b.1.hidden = false := hB.1
  -- But hHidden says a.1.hidden ≠ b.1.hidden
  rw [ha_false, hb_false] at hHidden
  exact hHidden rfl

/-- Main witness: LagEvent via lag_of_twist_and_hidden_step. -/
theorem lag_event_witness :
    LagEvent toySemantics toyObs toyTargetObs α₁ ToyPath.step :=
  lag_of_twist_and_hidden_step toySemantics toyTargetObs α₁ ToyPath.step
    step_depends_on_hidden x x' x_ne_x' holonomy_x_x' compatible_step_x

/-! ## 6. Witness: ¬ FactorsHolonomy -/

/-- The 2-cell α₂ : p ⇒ r. -/
def α₂ : ToyDef ToyPath.p ToyPath.r := ToyDef.pr

/-- Trivial 1D summary: all paths have the same code. -/
def trivialSummary : Summary (P := Unit) Unit := fun {_ _} _ => ()

/-- Holonomy for α₂ at (x, x') is False (because R_r is empty). -/
theorem not_holonomy_α₂_x_x' : ¬ HolonomyRel toySemantics toyObs toyTargetObs α₂ x x' := by
  intro ⟨y, _, hTransportR⟩
  -- Transport r x' y requires R_r, which is False
  exact hTransportR

/-- The holonomies of α₁ and α₂ differ. -/
theorem holonomies_differ :
    ¬ RelEq (HolonomyRel toySemantics toyObs toyTargetObs α₁)
            (HolonomyRel toySemantics toyObs toyTargetObs α₂) := by
  intro hEq
  -- At (x, x'): α₁ gives True, α₂ gives False
  have h1 : HolonomyRel toySemantics toyObs toyTargetObs α₁ x x' := holonomy_x_x'
  have h2 : HolonomyRel toySemantics toyObs toyTargetObs α₂ x x' := (hEq x x').mp h1
  exact not_holonomy_α₂_x_x' h2

/-- Main witness: ¬ FactorsHolonomy. -/
theorem not_factors_holonomy :
    ¬ FactorsHolonomy toySemantics toyObs toyTargetObs trivialSummary :=
  witness_no_factor toySemantics toyObs toyTargetObs trivialSummary
    α₁ α₂ rfl rfl holonomies_differ

/-! ## 7. Scheduling (Cheap Coverage) -/

/-- Trivial scheduling on Nat. -/
def toyScheduling : Scheduling (P := Unit) Nat where
  c := fun _ => ()
  mono := fun _ => reach_refl ()
  cofinal := fun _ => ⟨0, reach_refl ()⟩

/-! ## 8. AutoRegulated and Obstruction -/

/-- Empty gauge: all corrected transports are empty. -/
def emptyGauge : Gauge (P := Unit) toyObs toyTargetObs :=
  fun {_ _} _ => fun _ _ => False

/-- The cell for α₁. -/
def cell₁ : Cell (P := Unit) := ⟨(), (), ToyPath.p, ToyPath.q, ⟨ToyDef.pq⟩⟩

/-- AutoRegulated on empty set is trivially true. -/
theorem autoRegulated_empty :
    AutoRegulated (P := Unit) toySemantics toyObs toyTargetObs ∅ := by
  refine ⟨emptyGauge, ?_⟩
  intro c hc
  exact absurd hc (Set.notMem_empty c)

/-- ¬ Obstruction: empty gauge has no twisted corrected holonomy. -/
theorem not_obstruction_any (J : Set (Cell (P := Unit))) :
    ¬ Obstruction (P := Unit) toySemantics toyObs toyTargetObs J := by
  intro hObs
  -- Instantiate at emptyGauge
  obtain ⟨c, _, hWitness⟩ := hObs emptyGauge
  -- Unpack the cell
  obtain ⟨h, k, pathP, pathQ, ⟨def_α⟩⟩ := c
  obtain ⟨xW, x'W, _, hCorrHol⟩ := hWitness
  -- CorrectedHolonomy with emptyGauge is always False
  -- CorrectedHolonomy = relComp (CorrectedTransport p) (relConverse (CorrectedTransport q))
  -- CorrectedTransport = relComp (Transport) emptyGauge
  -- Since emptyGauge is always False, CorrectedTransport is always False
  -- Hence CorrectedHolonomy is always False
  obtain ⟨y, hCT_p, _⟩ := hCorrHol
  -- CorrectedTransport p xW y = ∃ z, Transport p xW z ∧ emptyGauge _ z y
  obtain ⟨z, _, hEmpty⟩ := hCT_p
  exact hEmpty

/-! ## 9. Axiom Audit -/

#print axioms toyHistoryGraph
#print axioms toySemantics
#print axioms twisted_holonomy_witness
#print axioms lag_event_witness
#print axioms not_factors_holonomy
#print axioms toyScheduling
#print axioms autoRegulated_empty
#print axioms not_obstruction_any

end PrimitiveHolonomy
