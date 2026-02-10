import RevHalt.Theory.PrimitiveHolonomy
import Mathlib

/-!
# Primitive Holonomy: Physics Bridge

This file formalizes the translation of RevHalt's topological structures into
Standard Model concepts (Baryogenesis, ABJ Anomaly, Sphalerons).

Ref: `docs/PRIMITIVE_HOLONOMY_PHYSICS.md`

## Key Concepts:
1.  **Weighted Relations**: Replacing `Prop` with a semantic weight (e.g., probability/amplitude)
    to quantify asymmetry.
2.  **C-Symmetry**: Involution on states.
3.  **Charges (B, L, N_CS)**: Observable quantities defined on states.
4.  **ABJ Anomaly**: The coupling law relating topological twist (holonomy) to charge variation.
-/

namespace PrimitiveHolonomy.Physics

universe u v w

-- ============================================================
-- 1. WEIGHTED SEMANTICS
-- ============================================================

/-- Weighted Relation: S → S → W instead of S → S → Prop. -/
def WeightedRel (S : Type u) (W : Type w) := S → S → W

variable {P : Type u} [HistoryGraph P]

/-- Semantics with weights.
    We require W to have a Semiring structure (provides +, *, 0, 1). -/
structure WeightedSemantics (S : Type u) (W : Type w) [Semiring W] where
  sem : {h k : P} → HistoryGraph.Path h k → WeightedRel S W

-- ============================================================
-- 2. PHYSICAL OBSERVABLES & SYMMETRIES
-- ============================================================

structure ParticlePhysics (S : Type u) where
  /-- Charge Conjugation: an involution on the micro-states. -/
  C : S → S
  C_invol : ∀ s, C (C s) = s

  /-- Baryon Number (B). -/
  B : S → Int
  /-- B is odd under C. -/
  B_odd : ∀ s, B (C s) = - B s

  /-- Lepton Number (L). -/
  L : S → Int
  L_odd : ∀ s, L (C s) = - L s

  /-- Chern-Simons Number / Topological Index (N_CS).
      Note: N_CS is typically CP-odd, but here we model the index itself. -/
  N_CS : S → Int

-- ============================================================
-- 3. THE ANOMALY CONTRACT
-- ============================================================

/-- Delta(B+L) across a transition `s1 -> s2`. -/
def DeltaBL {S : Type u} (phys : ParticlePhysics S) (s1 s2 : S) : Int :=
  (phys.B s2 - phys.B s1) + (phys.L s2 - phys.L s1)

/-- Delta topological index N_CS across a transition `s1 -> s2`. -/
def DeltaNCS {S : Type u} (phys : ParticlePhysics S) (s1 s2 : S) : Int :=
  phys.N_CS s2 - phys.N_CS s1

/--
  **ABJ Anomaly Law**:
  A transition `p` respects the ABJ anomaly if the change in (B+L)
  is proportional to the change in topological sector (N_CS).

  Δ(B+L) = 2 * N_f * ΔN_CS
-/
def SatisfiesABJ {S : Type u} (phys : ParticlePhysics S) (N_f : Int)
    (s1 s2 : S) : Prop :=
  DeltaBL phys s1 s2 = 2 * N_f * DeltaNCS phys s1 s2

/--
  **Sphaleron Gate**:
  A transition is a "Sphaleron" if it changes the topological sector.
-/
def IsSphaleron {S : Type u} (phys : ParticlePhysics S) (s1 s2 : S) : Prop :=
  phys.N_CS s1 ≠ phys.N_CS s2

theorem deltaNCS_ne_zero_of_isSphaleron {S : Type u}
    (phys : ParticlePhysics S) (s1 s2 : S) :
    IsSphaleron phys s1 s2 → DeltaNCS phys s1 s2 ≠ 0 := by
  intro hSph hΔ
  apply hSph
  exact (sub_eq_zero.mp hΔ).symm

theorem deltaBL_ne_zero_of_satisfiesABJ_of_isSphaleron
    {S : Type u} (phys : ParticlePhysics S) (N_f : Int) (s1 s2 : S)
    (hABJ : SatisfiesABJ phys N_f s1 s2)
    (hNf : N_f ≠ 0)
    (hSph : IsSphaleron phys s1 s2) :
    DeltaBL phys s1 s2 ≠ 0 := by
  have hΔN : DeltaNCS phys s1 s2 ≠ 0 :=
    deltaNCS_ne_zero_of_isSphaleron phys s1 s2 hSph
  have hK : (2 * N_f) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hNf
  rw [hABJ]
  exact mul_ne_zero hK hΔN

-- ============================================================
-- 4. BARYOGENESIS THEOREMS (Sketch)
-- ============================================================

variable {S : Type u} {W : Type w} [Semiring W]

/--
  **Symmetric Dynamics**:
  The dynamics commutes with C conjugation.
  W(s1 -> s2) = W(C(s1) -> C(s2)).
-/
def C_Symmetric_Dynamics
    (sem : WeightedSemantics (P := P) S W)
    (phys : ParticlePhysics S) : Prop :=
  ∀ {h k : P} (p : HistoryGraph.Path h k) (s1 s2 : S),
    sem.sem p s1 s2 = sem.sem p (phys.C s1) (phys.C s2)

/- 
  **No Bias Theorem**:
  If dynamics are C-symmetric and we start from a C-symmetric distribution,
  the expected Baryon number remains 0.
-/

/-- C-symmetric (C-invariant) distribution on micro-states. -/
def CInvariantDistribution {S : Type u} (phys : ParticlePhysics S) (μ : S → Rat) : Prop :=
  ∀ s, μ (phys.C s) = μ s

/-- Expected baryon number for a finitely supported (here finite-state) distribution. -/
def ExpectedB {S : Type u} [Fintype S] (phys : ParticlePhysics S) (μ : S → Rat) : Rat :=
  ∑ s : S, μ s * (phys.B s : Rat)

theorem expectedB_eq_neg_expectedB_of_CInvariantDistribution
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (μ : S → Rat)
    (hμ : CInvariantDistribution phys μ) :
    ExpectedB phys μ = - ExpectedB phys μ := by
  unfold ExpectedB
  let e : Equiv S S :=
    { toFun := phys.C
      invFun := phys.C
      left_inv := phys.C_invol
      right_inv := phys.C_invol }
  calc
    (∑ s : S, μ s * (phys.B s : Rat))
      = ∑ s : S, μ (e s) * (phys.B (e s) : Rat) := by
          exact
            Fintype.sum_equiv e
              (fun s : S => μ s * (phys.B s : Rat))
              (fun s : S => μ (e s) * (phys.B (e s) : Rat))
              (by
                intro x
                have hCC : e (e x) = x := by
                  simpa [e] using phys.C_invol x
                calc
                  μ x * (phys.B x : Rat)
                      = μ (e (e x)) * (phys.B (e (e x)) : Rat) := by simp [hCC]
                  _ = (fun s : S => μ (e s) * (phys.B (e s) : Rat)) (e x) := by rfl)
    _ = ∑ s : S, - (μ s * (phys.B s : Rat)) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          have hμs : μ (phys.C s) = μ s := hμ s
          have hBs : (phys.B (phys.C s) : Rat) = - (phys.B s : Rat) := by
            exact_mod_cast (phys.B_odd s)
          calc
            μ (e s) * (phys.B (e s) : Rat)
                = μ (phys.C s) * (phys.B (phys.C s) : Rat) := by rfl
            _ = μ s * (-(phys.B s : Rat)) := by simp [hμs, hBs]
            _ = - (μ s * (phys.B s : Rat)) := by ring
    _ = - ∑ s : S, μ s * (phys.B s : Rat) := by
          exact
            (Finset.sum_neg_distrib (s := (Finset.univ : Finset S))
              (f := fun s : S => μ s * (phys.B s : Rat)))

theorem zero_bias_of_symmetric_dynamics
    [Fintype S]
    (sem : WeightedSemantics (P := P) S W)
    (phys : ParticlePhysics S)
    (_hSym : C_Symmetric_Dynamics sem phys)
    (μ : S → Rat)
    (hμ : CInvariantDistribution phys μ) :
    ExpectedB phys μ = 0 := by
  have hneg : ExpectedB phys μ = - ExpectedB phys μ :=
    expectedB_eq_neg_expectedB_of_CInvariantDistribution phys μ hμ
  have hplus : ExpectedB phys μ + ExpectedB phys μ = 0 := by
    linarith [hneg]
  have hmul : (2 : Rat) * ExpectedB phys μ = 0 := by
    simpa [two_mul] using hplus
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- Concentration hypothesis: all mass is on one C-pair `(s, C s)`. -/
def TwoStateSupport {S : Type u} (phys : ParticlePhysics S) (μ : S → Rat) (s : S) : Prop :=
  ∀ t : S, t ≠ s → t ≠ phys.C s → μ t = 0

/-- C-asymmetric selection on a pair `(s, C s)` (lag-like orientation witness). -/
def LagBiasedSelection {S : Type u} (phys : ParticlePhysics S) (μ : S → Rat) (s : S) : Prop :=
  μ s ≠ μ (phys.C s)

/-- On a pure C-pair support, expected baryon number is an explicit biased pair formula. -/
theorem expectedB_pair_formula
    {S : Type u} [Fintype S] [DecidableEq S]
    (phys : ParticlePhysics S)
    (μ : S → Rat)
    (s : S)
    (hCs : phys.C s ≠ s)
    (hSupp : TwoStateSupport phys μ s) :
    ExpectedB phys μ = (μ s - μ (phys.C s)) * (phys.B s : Rat) := by
  unfold TwoStateSupport at hSupp
  let f : S → Rat := fun t => μ t * (phys.B t : Rat)
  have hs : s ∈ (Finset.univ : Finset S) := by simp
  have hCsIn : phys.C s ∈ (Finset.univ.erase s : Finset S) := by simp [hCs]
  have hsplit1 :
      (∑ t : S, f t) = f s + Finset.sum (Finset.univ.erase s) f := by
    have hsplit1' :
        (∑ t : S, f t) = Finset.sum (Finset.univ.erase s) f + f s := by
      exact
        (Finset.sum_erase_add (s := (Finset.univ : Finset S)) (a := s) (f := f) hs).symm
    calc
      (∑ t : S, f t) = Finset.sum (Finset.univ.erase s) f + f s := hsplit1'
      _ = f s + Finset.sum (Finset.univ.erase s) f := by ring
  have hsplit2 :
      Finset.sum (Finset.univ.erase s) f =
        f (phys.C s) + Finset.sum ((Finset.univ.erase s).erase (phys.C s)) f := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := (Finset.univ.erase s : Finset S)) (a := phys.C s) (f := f) hCsIn).symm
  have hrestZero : Finset.sum ((Finset.univ.erase s).erase (phys.C s)) f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have ht_ne_Cs : t ≠ phys.C s := (Finset.mem_erase.mp ht).1
    have ht_mem_erase_s : t ∈ (Finset.univ.erase s) := (Finset.mem_erase.mp ht).2
    have ht_ne_s : t ≠ s := (Finset.mem_erase.mp ht_mem_erase_s).1
    have hμ0 : μ t = 0 := hSupp t ht_ne_s ht_ne_Cs
    simp [hμ0]
  calc
    ExpectedB phys μ
        = ∑ t : S, f t := by rfl
    _ = f s + Finset.sum (Finset.univ.erase s) f := hsplit1
    _ = f s + (f (phys.C s) + Finset.sum ((Finset.univ.erase s).erase (phys.C s)) f) := by
          rw [hsplit2]
    _ = f s + f (phys.C s) := by simp [hrestZero]
    _ = μ s * (phys.B s : Rat) + μ (phys.C s) * (phys.B (phys.C s) : Rat) := by rfl
    _ = μ s * (phys.B s : Rat) + μ (phys.C s) * (-(phys.B s : Rat)) := by
          have hBodd : (phys.B (phys.C s) : Rat) = - (phys.B s : Rat) := by
            exact_mod_cast (phys.B_odd s)
          rw [hBodd]
    _ = (μ s - μ (phys.C s)) * (phys.B s : Rat) := by ring

/-- Positive direction: lag-biased selection on a C-pair implies non-zero baryon expectation. -/
theorem expectedB_ne_zero_of_lagBiasedSelection
    {S : Type u} [Fintype S] [DecidableEq S]
    (phys : ParticlePhysics S)
    (μ : S → Rat)
    (s : S)
    (hCs : phys.C s ≠ s)
    (hSupp : TwoStateSupport phys μ s)
    (hLag : LagBiasedSelection phys μ s)
    (hB : phys.B s ≠ 0) :
    ExpectedB phys μ ≠ 0 := by
  have hFormula :
      ExpectedB phys μ = (μ s - μ (phys.C s)) * (phys.B s : Rat) :=
    expectedB_pair_formula phys μ s hCs hSupp
  rw [hFormula]
  have hDiff : (μ s - μ (phys.C s)) ≠ 0 := sub_ne_zero.mpr hLag
  have hB_rat : (phys.B s : Rat) ≠ 0 := by exact_mod_cast hB
  exact mul_ne_zero hDiff hB_rat

-- ============================================================
-- 4.1 LAG -> SELECTION BIAS (formal bridge, qualitative)
-- ============================================================

section LagSelectionBridge

/-- Compatibility indicator on a fixed fiber (1 if compatible, else 0). -/
def CompatibilityIndicator
    {S V : Type u}
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)] :
    _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h → Rat :=
  fun x =>
    if _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x then 1 else 0

/-- A lag witness induces a strict bias on the compatibility indicator. -/
theorem lagEvent_implies_indicator_bias
    {S V : Type u}
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)]
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR obs target_obs α step) :
    ∃ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
      CompatibilityIndicator (P := P) semR obs target_obs step x ≠
      CompatibilityIndicator (P := P) semR obs target_obs step x' := by
  rcases hLag with ⟨x, x', _hxne, _hHol, hxCompat, hxNotCompat⟩
  refine ⟨x, x', ?_⟩
  have hx1 : CompatibilityIndicator (P := P) semR obs target_obs step x = 1 := by
    simp [CompatibilityIndicator, hxCompat]
  have hx0 : CompatibilityIndicator (P := P) semR obs target_obs step x' = 0 := by
    simp [CompatibilityIndicator, hxNotCompat]
  rw [hx1, hx0]
  norm_num

end LagSelectionBridge

-- ============================================================
-- 5. GAUGE-FIXING BRIDGE (Gribov-Singer shape)
-- ============================================================

/-!
This section gives an explicit bridge between:
- an external reading in terms of gauge-fixing (`local` vs `global`),
- and the internal PrimitiveHolonomy predicates.

It is a *formal correspondence layer* only. It does not claim that the open
continuum problem is solved.
-/

section GaugeFixingBridge

variable {Sg Vg : Type u}

/-- Local gauge-fixing is possible on each cell in `J` under admissibility `OK`. -/
abbrev LocalGaugeFixable
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) : Prop :=
  _root_.PrimitiveHolonomy.LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK J

/-- A single admissible gauge fixes all cells in `J`. -/
abbrev GlobalGaugeFixable
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) : Prop :=
  _root_.PrimitiveHolonomy.AutoRegulatedWrt (P := P) sem obs target_obs OK J

/-- Gribov-type obstruction: every admissible global gauge fails on some cell in `J`. -/
abbrev GaugeFixingObstructed
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) : Prop :=
  _root_.PrimitiveHolonomy.ObstructionWrt (P := P) sem obs target_obs OK J

/-- External-style statement: local repair exists, but no global admissible repair exists, on one cofinal future. -/
abbrev LocalButNotGlobalCofinal
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop) : Prop :=
  ∃ C : Set P, _root_.PrimitiveHolonomy.Cofinal (P := P) C ∧
    _root_.PrimitiveHolonomy.LocallyAutoRegulatedWrt (P := P) sem obs target_obs OK (_root_.PrimitiveHolonomy.CellsOver (P := P) C) ∧
    ¬ _root_.PrimitiveHolonomy.AutoRegulatedWrt (P := P) sem obs target_obs OK (_root_.PrimitiveHolonomy.CellsOver (P := P) C)

theorem obstructed_implies_not_globalGaugeFixable
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) :
    GaugeFixingObstructed sem obs target_obs OK J →
      ¬ GlobalGaugeFixable sem obs target_obs OK J := by
  exact _root_.PrimitiveHolonomy.not_AutoRegulatedWrt_of_ObstructionWrt (P := P) sem obs target_obs OK J

theorem globalGaugeFixable_implies_not_obstructed
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) :
    GlobalGaugeFixable sem obs target_obs OK J →
      ¬ GaugeFixingObstructed sem obs target_obs OK J := by
  exact _root_.PrimitiveHolonomy.not_ObstructionWrt_of_AutoRegulatedWrt (P := P) sem obs target_obs OK J

theorem globalGaugeFixable_iff_goodIntersection_nonempty
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) :
    GlobalGaugeFixable sem obs target_obs OK J ↔
      _root_.PrimitiveHolonomy.GoodGaugeIntersectionWrt (P := P) sem obs target_obs OK J := by
  exact _root_.PrimitiveHolonomy.autoRegulatedWrt_iff_goodGaugeIntersection_nonempty (P := P) sem obs target_obs OK J

theorem localGaugeFixable_iff_perCell_goodGauge
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) :
    LocalGaugeFixable sem obs target_obs OK J ↔
      ∀ c, c ∈ J → ∃ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs,
        _root_.PrimitiveHolonomy.GoodGaugeForCellWrt (P := P) sem obs target_obs OK c φ := by
  exact _root_.PrimitiveHolonomy.locallyAutoRegulatedWrt_iff_goodGaugeForCell_nonempty (P := P) sem obs target_obs OK J

theorem obstruction_iff_twisted_witness_per_admissible_gauge
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P))) :
    GaugeFixingObstructed sem obs target_obs OK J ↔
      ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
        ∃ c, c ∈ J ∧ _root_.PrimitiveHolonomy.TwistedOnCell (P := P) sem obs target_obs φ c := by
  exact _root_.PrimitiveHolonomy.obstructionWrt_iff_twistedOnCell (P := P) sem obs target_obs OK J

theorem localFlatButObstructedCofinal_implies_localButNotGlobal
    (sem : _root_.PrimitiveHolonomy.Semantics P Sg) (obs : Sg → Vg) (target_obs : P → Vg)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop) :
    _root_.PrimitiveHolonomy.LocalFlatButObstructedCofinalWrt (P := P) sem obs target_obs OK →
      LocalButNotGlobalCofinal sem obs target_obs OK := by
  intro h
  exact _root_.PrimitiveHolonomy.localAndNotAutoRegulatedWrt_of_localFlatButObstructedCofinalWrt
    (P := P) sem obs target_obs OK h

end GaugeFixingBridge

end PrimitiveHolonomy.Physics
