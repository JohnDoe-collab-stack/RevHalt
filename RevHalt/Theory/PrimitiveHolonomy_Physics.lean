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
-- 3.1 TOPOLOGY -> ABJ BRIDGE (missing central coupling layer)
-- ============================================================

section TopologyToABJBridge

variable {S V : Type w}

/-- ABJ holds on every sphaleron (topological-jump) pair. -/
def ABJOnSphaleronPairs (phys : ParticlePhysics S) (N_f : Int) : Prop :=
  ∀ s1 s2 : S, IsSphaleron phys s1 s2 → SatisfiesABJ phys N_f s1 s2

/-- Bridge contract: every twisted cell yields (at least) one sphaleron pair. -/
def TwistToSphaleronBridge
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P)),
    _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR obs target_obs φ c →
      ∃ s1 s2 : S, IsSphaleron phys s1 s2

/-- Concrete micro-level contract: a twisted corrected-holonomy witness always carries
an `N_CS` jump between the two witness states. -/
def NCSJumpOnTwistedWitness
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P)),
    let ⟨h, _, _, _, ⟨α⟩⟩ := c
    ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
      x ≠ x' →
      _root_.PrimitiveHolonomy.CorrectedHolonomy (P := P) semR obs target_obs φ α x x' →
      phys.N_CS x.1 ≠ phys.N_CS x'.1

/-- `N_CS` separates points inside a fixed observation fiber. -/
def NCSInjectiveOnFiber
    (phys : ParticlePhysics S) (obs : S → V) (target_obs : P → V) (h : P) : Prop :=
  Function.Injective (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h => phys.N_CS x.1)

/-- Fiberwise version: `N_CS` is injective on every observation fiber. -/
def NCSInjectiveOnAllFibers
    (phys : ParticlePhysics S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ h : P, NCSInjectiveOnFiber (P := P) phys obs target_obs h

/-- Fiberwise `N_CS`-injectivity already implies the twisted-witness `N_CS` jump contract. -/
theorem ncsJumpOnTwistedWitness_of_ncsInjectiveOnAllFibers
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hFib : NCSInjectiveOnAllFibers (P := P) phys obs target_obs) :
    NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs := by
  intro φ c
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  intro x x' hxne _hHol hEq
  exact hxne ((hFib h) hEq)

/-- If `N_CS` is injective on micro-states, any twisted witness is automatically
an `N_CS`-jump witness. -/
theorem ncsJumpOnTwistedWitness_of_ncs_injective
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hInj : Function.Injective phys.N_CS) :
    NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs := by
  intro φ c
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  intro x x' hxne _hHol hEq
  apply hxne
  exact Subtype.ext (hInj hEq)

/-- Canonical physics structure on `LagState Y Int`:
`C` flips the hidden integer, and `N_CS` is the hidden component. -/
def lagStateIntPhysics (Y : Type) : ParticlePhysics (_root_.PrimitiveHolonomy.LagState Y Int) where
  C := fun s => ⟨s.visible, -s.hidden⟩
  C_invol := by
    intro s
    cases s
    simp
  B := fun s => s.hidden
  B_odd := by
    intro s
    cases s
    simp
  L := fun s => s.hidden
  L_odd := by
    intro s
    cases s
    simp
  N_CS := fun s => s.hidden

/-- In the canonical `LagState Y Int` model with `B = L = N_CS = hidden`,
the ABJ law holds on sphaleron pairs for one family (`N_f = 1`). -/
theorem satisfiesABJ_lagStateIntPhysics_nf_one
    {Y : Type} (s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int) :
    SatisfiesABJ (lagStateIntPhysics (Y := Y)) 1 s1 s2 := by
  unfold SatisfiesABJ DeltaBL DeltaNCS
  simp [lagStateIntPhysics]
  ring

/-- In the canonical `LagState Y Int` model with `B = L = N_CS = hidden`,
the ABJ law holds on sphaleron pairs for one family (`N_f = 1`). -/
theorem abjOnSphaleronPairs_lagStateIntPhysics_nf_one
    {Y : Type} :
    ABJOnSphaleronPairs (lagStateIntPhysics (Y := Y)) 1 := by
  intro s1 s2 _hSph
  exact satisfiesABJ_lagStateIntPhysics_nf_one (Y := Y) s1 s2

/-- In the product model `X = Y × Int` with observable `lagObs`,
twisted witnesses automatically carry a topological jump (`ΔN_CS ≠ 0`). -/
theorem ncsJumpOnTwistedWitness_of_lagState_hidden
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y) :
    NCSJumpOnTwistedWitness (P := P)
      (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
      (lagStateIntPhysics (Y := Y)) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs := by
  intro φ c
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  intro x x' hxne _hHol
  have hHidden : x.1.hidden ≠ x'.1.hidden :=
    _root_.PrimitiveHolonomy.hidden_ne_of_ne
      (P := P) (target_obs := target_obs) (h := h) (x := x) (x' := x') hxne
  simpa [lagStateIntPhysics] using hHidden

/-- A concrete `N_CS`-jump witness assumption yields the abstract
`TwistToSphaleronBridge` contract. -/
theorem twistToSphaleronBridge_of_ncsJumpOnTwistedWitness
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hNCS : NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs) :
    TwistToSphaleronBridge (P := P) phys semR obs target_obs := by
  intro φ c hTw
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  dsimp [_root_.PrimitiveHolonomy.TwistedOnCell] at hTw
  rcases hTw with ⟨x, x', hxne, hHol⟩
  have hJump : phys.N_CS x.1 ≠ phys.N_CS x'.1 :=
    hNCS φ ⟨h, k, p, q, ⟨α⟩⟩ x x' hxne hHol
  exact ⟨x.1, x'.1, hJump⟩

/-- Once the bridge contracts are assumed, any twisted cell forces a non-zero `Δ(B+L)`. -/
theorem deltaBL_ne_zero_of_twistedOnCell_of_bridges
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hNf : N_f ≠ 0)
    (hTwBridge : TwistToSphaleronBridge (P := P) phys semR obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR obs target_obs φ c) :
    ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  rcases hTwBridge φ c hTw with ⟨s1, s2, hSph⟩
  refine ⟨s1, s2, ?_⟩
  exact deltaBL_ne_zero_of_satisfiesABJ_of_isSphaleron
    phys N_f s1 s2 (hABJall s1 s2 hSph) hNf hSph

/-- One-shot concrete form:
if twisted witnesses are `N_CS`-jumping and ABJ holds on sphaleron pairs,
then any twisted cell forces a non-zero `Δ(B+L)`. -/
theorem deltaBL_ne_zero_of_twistedOnCell_of_ncsJump_and_abj
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hNf : N_f ≠ 0)
    (hNCS : NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR obs target_obs φ c) :
    ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  exact deltaBL_ne_zero_of_twistedOnCell_of_bridges
    (P := P) phys N_f semR obs target_obs hNf
    (twistToSphaleronBridge_of_ncsJumpOnTwistedWitness (P := P) phys semR obs target_obs hNCS)
    hABJall φ c hTw

/-- Intrinsic-fiber form:
if `N_CS` separates each fiber and ABJ holds on sphaleron pairs,
any twisted cell forces a non-zero `Δ(B+L)`. -/
theorem deltaBL_ne_zero_of_twistedOnCell_of_ncsInjectiveOnAllFibers_and_abj
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (hNf : N_f ≠ 0)
    (hFib : NCSInjectiveOnAllFibers (P := P) phys obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR obs target_obs φ c) :
    ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  exact deltaBL_ne_zero_of_twistedOnCell_of_ncsJump_and_abj
    (P := P) phys N_f semR obs target_obs hNf
    (ncsJumpOnTwistedWitness_of_ncsInjectiveOnAllFibers (P := P) phys semR obs target_obs hFib)
    hABJall φ c hTw

/-- Canonical `LagState` form: in the model `N_CS = hidden`,
twist implies a non-zero `Δ(B+L)` as soon as ABJ holds on sphaleron pairs. -/
theorem deltaBL_ne_zero_of_twistedOnCell_of_lagState_hidden_and_abj
    {Y : Type} (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    (hNf : N_f ≠ 0)
    (hABJall : ABJOnSphaleronPairs (lagStateIntPhysics (Y := Y)) N_f)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs φ c) :
    ∃ s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int,
      DeltaBL (lagStateIntPhysics (Y := Y)) s1 s2 ≠ 0 := by
  exact deltaBL_ne_zero_of_twistedOnCell_of_ncsJump_and_abj
    (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
    (phys := lagStateIntPhysics (Y := Y)) N_f semR
    (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs hNf
    (ncsJumpOnTwistedWitness_of_lagState_hidden (P := P) (Y := Y) semR target_obs)
    hABJall φ c hTw

/-- Canonical `LagState` form without external ABJ assumption:
for `N_f = 1`, twisted cells force non-zero `Δ(B+L)`. -/
theorem deltaBL_ne_zero_of_twistedOnCell_of_lagState_hidden
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := P))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs φ c) :
    ∃ s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int,
      DeltaBL (lagStateIntPhysics (Y := Y)) s1 s2 ≠ 0 := by
  exact deltaBL_ne_zero_of_twistedOnCell_of_lagState_hidden_and_abj
    (P := P) (Y := Y) (N_f := 1) semR target_obs
    (by norm_num)
    (abjOnSphaleronPairs_lagStateIntPhysics_nf_one (Y := Y))
    φ c hTw

/-- Obstruction + bridge contracts imply: every admissible gauge has some
topological pair with non-zero `Δ(B+L)`. -/
theorem obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (hNf : N_f ≠ 0)
    (hTwBridge : TwistToSphaleronBridge (P := P) phys semR obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) semR obs target_obs OK J) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
      ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  have hObsTw :
      ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
        ∃ c, c ∈ J ∧ _root_.PrimitiveHolonomy.TwistedOnCell (P := P) semR obs target_obs φ c := by
    exact
      (_root_.PrimitiveHolonomy.obstructionWrt_iff_twistedOnCell
        (P := P) semR obs target_obs OK J).1 hObs
  intro φ hOK
  rcases hObsTw φ hOK with ⟨c, _hcJ, hTw⟩
  exact deltaBL_ne_zero_of_twistedOnCell_of_bridges
    (P := P) phys N_f semR obs target_obs hNf hTwBridge hABJall φ c hTw

/-- Concrete obstruction form (no abstract bridge argument):
if twisted witnesses force `N_CS` jumps and ABJ holds on sphaleron pairs,
then each admissible gauge has a non-zero `Δ(B+L)` witness. -/
theorem obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsJump_and_abj
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (hNf : N_f ≠ 0)
    (hNCS : NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) semR obs target_obs OK J) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
      ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  exact obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge
    (P := P) phys N_f semR obs target_obs OK J hNf
    (twistToSphaleronBridge_of_ncsJumpOnTwistedWitness (P := P) phys semR obs target_obs hNCS)
    hABJall hObs

/-- Obstruction form with intrinsic fiberwise `N_CS` separation. -/
theorem obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsInjectiveOnAllFibers_and_abj
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (hNf : N_f ≠ 0)
    (hFib : NCSInjectiveOnAllFibers (P := P) phys obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) semR obs target_obs OK J) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
      ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  exact obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsJump_and_abj
    (P := P) phys N_f semR obs target_obs OK J hNf
    (ncsJumpOnTwistedWitness_of_ncsInjectiveOnAllFibers (P := P) phys semR obs target_obs hFib)
    hABJall hObs

/-- Canonical `LagState` obstruction form without external ABJ assumption:
for `N_f = 1`, each admissible gauge has a non-zero `Δ(B+L)` witness. -/
theorem obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_lagState_hidden
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs OK J) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs, OK φ →
      ∃ s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int,
        DeltaBL (lagStateIntPhysics (Y := Y)) s1 s2 ≠ 0 := by
  exact obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsJump_and_abj
    (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
    (phys := lagStateIntPhysics (Y := Y)) (N_f := 1)
    semR (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs OK J
    (by norm_num)
    (ncsJumpOnTwistedWitness_of_lagState_hidden (P := P) (Y := Y) semR target_obs)
    (abjOnSphaleronPairs_lagStateIntPhysics_nf_one (Y := Y))
    hObs

/-- Cofinal version: if the system is locally flat but globally obstructed on a cofinal
future, and the `N_CS`/ABJ bridge contracts hold, then on that same cofinal future
every admissible gauge admits a non-zero `Δ(B+L)` witness. -/
theorem localFlatButObstructedCofinalWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (hNf : N_f ≠ 0)
    (hNCS : NCSJumpOnTwistedWitness (P := P) phys semR obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (hLFO : _root_.PrimitiveHolonomy.LocalFlatButObstructedCofinalWrt (P := P) semR obs target_obs OK) :
    ∃ C : Set P, _root_.PrimitiveHolonomy.Cofinal (P := P) C ∧
      ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs,
        OK φ → ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  rcases hLFO with ⟨C, hCof, _hLocal, hObs⟩
  refine ⟨C, hCof, ?_⟩
  exact
    obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsJump_and_abj
      (P := P) phys N_f semR obs target_obs OK (_root_.PrimitiveHolonomy.CellsOver (P := P) C)
      hNf hNCS hABJall hObs

/-- Cofinal obstruction form with intrinsic fiberwise `N_CS` separation. -/
theorem localFlatButObstructedCofinalWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsInjectiveOnAllFibers_and_abj
    (phys : ParticlePhysics S) (N_f : Int)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (hNf : N_f ≠ 0)
    (hFib : NCSInjectiveOnAllFibers (P := P) phys obs target_obs)
    (hABJall : ABJOnSphaleronPairs phys N_f)
    (hLFO : _root_.PrimitiveHolonomy.LocalFlatButObstructedCofinalWrt (P := P) semR obs target_obs OK) :
    ∃ C : Set P, _root_.PrimitiveHolonomy.Cofinal (P := P) C ∧
      ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs,
        OK φ → ∃ s1 s2 : S, DeltaBL phys s1 s2 ≠ 0 := by
  rcases hLFO with ⟨C, hCof, _hLocal, hObs⟩
  refine ⟨C, hCof, ?_⟩
  exact
    obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsInjectiveOnAllFibers_and_abj
      (P := P) phys N_f semR obs target_obs OK (_root_.PrimitiveHolonomy.CellsOver (P := P) C)
      hNf hFib hABJall hObs

/-- Canonical `LagState` cofinal-obstruction form without external ABJ assumption:
for `N_f = 1`, every admissible gauge on the obstructed cofinal future has a
non-zero `Δ(B+L)` witness. -/
theorem localFlatButObstructedCofinalWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_lagState_hidden
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs → Prop)
    (hLFO : _root_.PrimitiveHolonomy.LocalFlatButObstructedCofinalWrt (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs OK) :
    ∃ C : Set P, _root_.PrimitiveHolonomy.Cofinal (P := P) C ∧
      ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P)
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs,
        OK φ →
          ∃ s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int,
            DeltaBL (lagStateIntPhysics (Y := Y)) s1 s2 ≠ 0 := by
  exact localFlatButObstructedCofinalWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge
    (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
    (phys := lagStateIntPhysics (Y := Y)) (N_f := 1)
    semR (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs OK
    (by norm_num)
    (ncsJumpOnTwistedWitness_of_lagState_hidden (P := P) (Y := Y) semR target_obs)
    (abjOnSphaleronPairs_lagStateIntPhysics_nf_one (Y := Y))
    hLFO

end TopologyToABJBridge

-- ============================================================
-- 3.2 CONCRETE TWO-STATE INSTANCE (explicit N_CS-separating model)
-- ============================================================

section TwoStateInstance

inductive TwoState where
  | a
  | b
  deriving DecidableEq, Fintype

def twoC : TwoState → TwoState
  | .a => .b
  | .b => .a

def twoB : TwoState → Int
  | .a => 1
  | .b => -1

def twoL : TwoState → Int
  | .a => 1
  | .b => -1

def twoNCS : TwoState → Int
  | .a => 0
  | .b => 1

def twoStatePhysics : ParticlePhysics TwoState where
  C := twoC
  C_invol := by
    intro s
    cases s <;> rfl
  B := twoB
  B_odd := by
    intro s
    cases s <;> decide
  L := twoL
  L_odd := by
    intro s
    cases s <;> decide
  N_CS := twoNCS

theorem twoNCS_injective : Function.Injective twoStatePhysics.N_CS := by
  intro s t h
  cases s <;> cases t <;> simp [twoStatePhysics, twoNCS] at h ⊢

/-- In the explicit two-state model, `NCSJumpOnTwistedWitness` is automatic
for any semantics/observable/fiber map. -/
theorem ncsJumpOnTwistedWitness_twoState
    {V : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P TwoState)
    (obs : TwoState → V) (target_obs : P → V) :
    NCSJumpOnTwistedWitness (P := P) (S := TwoState) (V := V)
      twoStatePhysics semR obs target_obs := by
  exact ncsJumpOnTwistedWitness_of_ncs_injective
    (P := P) (S := TwoState) (V := V)
    twoStatePhysics semR obs target_obs twoNCS_injective

end TwoStateInstance

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

/-- One-step pushforward of a distribution along a weighted transition kernel. -/
def EvolveDist {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat) : S → Rat :=
  fun s2 => ∑ s1 : S, μ s1 * sem.sem p s1 s2

/-- Row-normalization of a one-step kernel (discrete Markov condition). -/
def IsMarkovKernel {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) : Prop :=
  ∀ s1 : S, ∑ s2 : S, sem.sem p s1 s2 = 1

/-- Detailed balance at distribution `μ` for one step `p`. -/
def DetailedBalance {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat) : Prop :=
  ∀ s1 s2 : S, μ s1 * sem.sem p s1 s2 = μ s2 * sem.sem p s2 s1

/-- Stationarity of `μ` under one-step evolution by `p`. -/
def StationaryDist {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat) : Prop :=
  ∀ s2 : S, EvolveDist (P := P) sem p μ s2 = μ s2

theorem stationary_of_detailedBalance_of_markov
    {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hDB : DetailedBalance (P := P) sem p μ)
    (hMk : IsMarkovKernel (P := P) sem p) :
    StationaryDist (P := P) sem p μ := by
  intro s2
  unfold EvolveDist
  calc
    (∑ s1 : S, μ s1 * sem.sem p s1 s2)
        = ∑ s1 : S, μ s2 * sem.sem p s2 s1 := by
            refine Finset.sum_congr rfl ?_
            intro s1 _hs
            exact hDB s1 s2
    _ = μ s2 * ∑ s1 : S, sem.sem p s2 s1 := by
          simp [Finset.mul_sum]
    _ = μ s2 * 1 := by rw [hMk s2]
    _ = μ s2 := by ring

theorem expectedB_evolve_eq_expectedB_of_stationary
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hStat : StationaryDist (P := P) sem p μ) :
    ExpectedB phys (EvolveDist (P := P) sem p μ) = ExpectedB phys μ := by
  unfold ExpectedB
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [hStat s]

/-- Net one-step baryon production under kernel evolution. -/
def DeltaExpectedB {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat) : Rat :=
  ExpectedB phys (EvolveDist (P := P) sem p μ) - ExpectedB phys μ

/-- No-go (equilibrium detailed-balance form):
under detailed balance + Markov normalization, one step cannot create net baryon expectation. -/
theorem deltaExpectedB_eq_zero_of_detailedBalance_of_markov
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hDB : DetailedBalance (P := P) sem p μ)
    (hMk : IsMarkovKernel (P := P) sem p) :
    DeltaExpectedB (P := P) phys sem p μ = 0 := by
  unfold DeltaExpectedB
  have hStat : StationaryDist (P := P) sem p μ :=
    stationary_of_detailedBalance_of_markov (P := P) sem p μ hDB hMk
  have hEq :
      ExpectedB phys (EvolveDist (P := P) sem p μ) = ExpectedB phys μ :=
    expectedB_evolve_eq_expectedB_of_stationary (P := P) phys sem p μ hStat
  linarith [hEq]

/-- Corollary: equilibrium detailed balance preserves zero baryon expectation in one step. -/
theorem zero_bias_of_detailedBalance
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hDB : DetailedBalance (P := P) sem p μ)
    (hMk : IsMarkovKernel (P := P) sem p)
    (hZero : ExpectedB phys μ = 0) :
    ExpectedB phys (EvolveDist (P := P) sem p μ) = 0 := by
  have hEq :
      ExpectedB phys (EvolveDist (P := P) sem p μ) = ExpectedB phys μ :=
    expectedB_evolve_eq_expectedB_of_stationary (P := P) phys sem p μ
      (stationary_of_detailedBalance_of_markov (P := P) sem p μ hDB hMk)
  rw [hEq, hZero]

/-- `n`-step evolution by iterating the same one-step kernel. -/
def EvolveDistN {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) : Nat → (S → Rat) → (S → Rat)
  | 0, μ => μ
  | n + 1, μ => EvolveDist (P := P) sem p (EvolveDistN sem p n μ)

theorem evolveDistN_eq_of_stationary
    {S : Type u} [Fintype S]
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hStat : StationaryDist (P := P) sem p μ) :
    ∀ n : Nat, EvolveDistN (P := P) sem p n μ = μ := by
  have hStatEq : EvolveDist (P := P) sem p μ = μ := funext hStat
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [EvolveDistN, ih, hStatEq]

theorem expectedB_evolveDistN_eq_expectedB_of_stationary
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hStat : StationaryDist (P := P) sem p μ) :
    ∀ n : Nat, ExpectedB phys (EvolveDistN (P := P) sem p n μ) = ExpectedB phys μ := by
  intro n
  rw [evolveDistN_eq_of_stationary (P := P) sem p μ hStat n]

theorem expectedB_evolveDistN_eq_expectedB_of_detailedBalance_of_markov
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hDB : DetailedBalance (P := P) sem p μ)
    (hMk : IsMarkovKernel (P := P) sem p) :
    ∀ n : Nat, ExpectedB phys (EvolveDistN (P := P) sem p n μ) = ExpectedB phys μ := by
  exact expectedB_evolveDistN_eq_expectedB_of_stationary (P := P) phys sem p μ
    (stationary_of_detailedBalance_of_markov (P := P) sem p μ hDB hMk)

/-- Net baryon production at step `n -> n+1` along iterated evolution. -/
def DeltaExpectedBStepN {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat) (n : Nat) : Rat :=
  ExpectedB phys (EvolveDistN (P := P) sem p (n + 1) μ) -
  ExpectedB phys (EvolveDistN (P := P) sem p n μ)

/-- Multi-step no-go:
under detailed balance + Markov normalization, every step has zero net baryon production. -/
theorem deltaExpectedBStepN_eq_zero_of_detailedBalance_of_markov
    {S : Type u} [Fintype S]
    (phys : ParticlePhysics S)
    (sem : WeightedSemantics (P := P) S Rat)
    {h k : P} (p : HistoryGraph.Path h k) (μ : S → Rat)
    (hDB : DetailedBalance (P := P) sem p μ)
    (hMk : IsMarkovKernel (P := P) sem p) :
    ∀ n : Nat, DeltaExpectedBStepN (P := P) phys sem p μ n = 0 := by
  intro n
  unfold DeltaExpectedBStepN
  have hInv := expectedB_evolveDistN_eq_expectedB_of_detailedBalance_of_markov
    (P := P) phys sem p μ hDB hMk
  rw [hInv (n + 1), hInv n]
  ring

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
    (sem : WeightedSemantics (P := P) S Rat)
    (phys : ParticlePhysics S)
    (hSym : C_Symmetric_Dynamics sem phys)
    {h k : P} (p : HistoryGraph.Path h k)
    (μ : S → Rat)
    (hμ : CInvariantDistribution phys μ) :
    ExpectedB phys (EvolveDist (P := P) sem p μ) = 0 := by
  have hμevolved : CInvariantDistribution phys (EvolveDist (P := P) sem p μ) := by
    intro s2
    unfold EvolveDist
    let e : Equiv S S :=
      { toFun := phys.C
        invFun := phys.C
        left_inv := phys.C_invol
        right_inv := phys.C_invol }
    calc
      (∑ s1 : S, μ s1 * sem.sem p s1 (phys.C s2))
          = ∑ s1 : S, μ (e s1) * sem.sem p (e s1) (phys.C s2) := by
              exact
                Fintype.sum_equiv e
                  (fun s1 : S => μ s1 * sem.sem p s1 (phys.C s2))
                  (fun s1 : S => μ (e s1) * sem.sem p (e s1) (phys.C s2))
                  (by
                    intro x
                    have hCC : e (e x) = x := by
                      simpa [e] using phys.C_invol x
                    calc
                      μ x * sem.sem p x (phys.C s2)
                          = μ (e (e x)) * sem.sem p (e (e x)) (phys.C s2) := by simp [hCC]
                      _ = (fun s1 : S => μ (e s1) * sem.sem p (e s1) (phys.C s2)) (e x) := by rfl)
      _ = ∑ s1 : S, μ s1 * sem.sem p s1 s2 := by
            refine Finset.sum_congr rfl ?_
            intro s1 _hs
            have hμs : μ (phys.C s1) = μ s1 := hμ s1
            have hsym : sem.sem p (phys.C s1) (phys.C s2) = sem.sem p s1 s2 := by
              exact (hSym p s1 s2).symm
            simp [e, hμs, hsym]
  have hneg :
      ExpectedB phys (EvolveDist (P := P) sem p μ) =
      - ExpectedB phys (EvolveDist (P := P) sem p μ) :=
    expectedB_eq_neg_expectedB_of_CInvariantDistribution
      phys (EvolveDist (P := P) sem p μ) hμevolved
  have hplus :
      ExpectedB phys (EvolveDist (P := P) sem p μ) +
      ExpectedB phys (EvolveDist (P := P) sem p μ) = 0 := by
    linarith [hneg]
  have hmul : (2 : Rat) * ExpectedB phys (EvolveDist (P := P) sem p μ) = 0 := by
    simpa [two_mul] using hplus
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- Concentration hypothesis: all mass is on one C-pair `(s, C s)`. -/
def TwoStateSupport {S : Type u} (phys : ParticlePhysics S) (μ : S → Rat) (s : S) : Prop :=
  ∀ t : S, t ≠ s → t ≠ phys.C s → μ t = 0

/-- C-asymmetric selection on a pair `(s, C s)` (lag-like orientation witness). -/
def LagBiasedSelection {S : Type u} (phys : ParticlePhysics S) (μ : S → Rat) (s : S) : Prop :=
  μ s ≠ μ (phys.C s)

/-- Distribution concentrated on two distinguished states `s` and `cs`. -/
def PairDistribution {S : Type u} [DecidableEq S] (s cs : S) (a b : Rat) : S → Rat :=
  fun t => if t = s then a else if t = cs then b else 0

theorem twoStateSupport_pairDistribution
    {S : Type u} [DecidableEq S] (phys : ParticlePhysics S) (s : S) (a b : Rat) :
    TwoStateSupport phys (PairDistribution s (phys.C s) a b) s := by
  intro t ht_ne_s ht_ne_cs
  simp [PairDistribution, ht_ne_s, ht_ne_cs]

theorem lagBiasedSelection_pairDistribution
    {S : Type u} [DecidableEq S] (phys : ParticlePhysics S) (s : S) (a b : Rat)
    (hCs : phys.C s ≠ s) (hab : a ≠ b) :
    LagBiasedSelection phys (PairDistribution s (phys.C s) a b) s := by
  have hsC : s ≠ phys.C s := by
    intro hs
    exact hCs hs.symm
  unfold LagBiasedSelection PairDistribution
  simpa [hCs, hsC] using hab

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

/-- Hypothesis: every lag witness on `(α, step)` is a conjugate pair under `phys.C`,
with no fixed point on that witness. -/
def LagConjugacyHypothesis
    {S V : Type w}
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop :=
  ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
    x ≠ x' →
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) semR obs target_obs α x x' →
    _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x →
    ¬ _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x' →
    x'.1 = phys.C x.1 ∧ phys.C x.1 ≠ x.1

/-- Equality-only version of `LagConjugacyHypothesis`. -/
def LagConjugacyEqHypothesis
    {S V : Type w}
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop :=
  ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
    x ≠ x' →
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) semR obs target_obs α x x' →
    _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x →
    ¬ _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x' →
    x'.1 = phys.C x.1

theorem lagConjugacyHypothesis_of_eq
    {S V : Type w}
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (hEq : LagConjugacyEqHypothesis (P := P) phys semR obs target_obs α step) :
    LagConjugacyHypothesis (P := P) phys semR obs target_obs α step := by
  intro x x' hxne hHol hx hx'
  refine ⟨hEq x x' hxne hHol hx hx', ?_⟩
  intro hFix
  apply hxne
  apply Subtype.ext
  exact ((hEq x x' hxne hHol hx hx').trans hFix).symm

/-- Canonical hidden-flip contract for lag witnesses in `LagState Y Int`. -/
def LagHiddenFlipWitness
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') : Prop :=
  ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h,
    x ≠ x' →
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α x x' →
    _root_.PrimitiveHolonomy.Compatible (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x →
    ¬ _root_.PrimitiveHolonomy.Compatible (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x' →
    x'.1.hidden = -x.1.hidden

/-- Pure topological version: holonomy witnesses already force opposite hidden signs
(independent of the later compatibility test). -/
def HolonomyHiddenFlipWitness
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h,
    x ≠ x' →
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α x x' →
    x'.1.hidden = -x.1.hidden

/-- Structural semantics hypothesis: every holonomy relation on `LagState Y Int`
flips the hidden component. -/
def SemanticsFlipsHiddenOnHolonomy
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y) : Prop :=
  ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h),
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α x x' →
    x'.1.hidden = -x.1.hidden

theorem holonomyHiddenFlipWitness_of_semanticsFlipsHiddenOnHolonomy
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hSemFlip : SemanticsFlipsHiddenOnHolonomy (P := P) semR target_obs) :
    HolonomyHiddenFlipWitness (P := P) semR target_obs α := by
  intro x x' _hxne hHol
  exact hSemFlip α x x' hHol

theorem lagHiddenFlipWitness_of_holonomyHiddenFlipWitness
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (hHolFlip : HolonomyHiddenFlipWitness (P := P) semR target_obs α) :
    LagHiddenFlipWitness (P := P) semR target_obs α step := by
  intro x x' hxne hHol _hx _hx'
  exact hHolFlip x x' hxne hHol

/-- Hidden-flip witness implies the equality-only conjugacy hypothesis
for the canonical `lagStateIntPhysics`. -/
theorem lagConjugacyEqHypothesis_lagStateInt_of_hiddenFlip
    {Y : Type}
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    (hFlip : LagHiddenFlipWitness (P := P) semR target_obs α step) :
    LagConjugacyEqHypothesis (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
      (lagStateIntPhysics (Y := Y)) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step := by
  intro x x' hxne hHol hx hx'
  have hHidden : x'.1.hidden = -x.1.hidden := hFlip x x' hxne hHol hx hx'
  have hVis : x'.1.visible = x.1.visible := by
    exact x'.2.trans x.2.symm
  cases xs : x.1 with
  | mk vis hid =>
    cases xs' : x'.1 with
    | mk vis' hid' =>
      have hVis' : vis' = vis := by
        simpa [xs, xs'] using hVis
      have hHid' : hid' = -hid := by
        simpa [xs, xs'] using hHidden
      subst hVis'
      subst hHid'
      simp [lagStateIntPhysics]

/-- Compatibility indicator on a fixed fiber (1 if compatible, else 0). -/
def CompatibilityIndicator
    {S V : Type w}
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k : P} (step : HistoryGraph.Path h k)
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)] :
    _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h → Rat :=
  fun x =>
    if _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x then 1 else 0

/-- A lag witness induces a strict bias on the compatibility indicator. -/
theorem lagEvent_implies_indicator_bias
    {S V : Type w}
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

/-- Under a conjugacy hypothesis, a lag event yields an explicit C-biased
two-point distribution. -/
theorem lagEvent_implies_lagBiasedSelection_under_conjugacy
    {S V : Type w}
    [DecidableEq S]
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)]
    (hConj : LagConjugacyHypothesis (P := P) phys semR obs target_obs α step)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR obs target_obs α step) :
    ∃ s : S, ∃ μ : S → Rat,
      LagBiasedSelection phys μ s ∧ TwoStateSupport phys μ s := by
  rcases hLag with ⟨x, x', hxne, hHol, hxCompat, hxNotCompat⟩
  rcases hConj x x' hxne hHol hxCompat hxNotCompat with ⟨hxConj, hCne⟩
  let a : Rat := CompatibilityIndicator (P := P) semR obs target_obs step x
  let b : Rat := CompatibilityIndicator (P := P) semR obs target_obs step x'
  let μ : S → Rat := PairDistribution x.1 (phys.C x.1) a b
  have ha : a = 1 := by
    unfold a CompatibilityIndicator
    simp [hxCompat]
  have hb : b = 0 := by
    unfold b CompatibilityIndicator
    simp [hxNotCompat]
  have hab : a ≠ b := by
    rw [ha, hb]
    norm_num
  refine ⟨x.1, μ, ?_, ?_⟩
  · -- C-biased selection on the pair
    dsimp [μ]
    exact lagBiasedSelection_pairDistribution phys x.1 a b hCne hab
  · -- support only on `{x, C x}`
    dsimp [μ]
    exact twoStateSupport_pairDistribution phys x.1 a b

/-- Variant with explicit non-fixed-point witness `phys.C s ≠ s`. -/
theorem lagEvent_implies_lagBiasedSelection_with_nonfixed_under_conjugacy
    {S V : Type w}
    [DecidableEq S]
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)]
    (hConj : LagConjugacyHypothesis (P := P) phys semR obs target_obs α step)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR obs target_obs α step) :
    ∃ s : S, ∃ μ : S → Rat,
      phys.C s ≠ s ∧ LagBiasedSelection phys μ s ∧ TwoStateSupport phys μ s := by
  rcases hLag with ⟨x, x', hxne, hHol, hxCompat, hxNotCompat⟩
  rcases hConj x x' hxne hHol hxCompat hxNotCompat with ⟨_hxConj, hCne⟩
  let a : Rat := CompatibilityIndicator (P := P) semR obs target_obs step x
  let b : Rat := CompatibilityIndicator (P := P) semR obs target_obs step x'
  let μ : S → Rat := PairDistribution x.1 (phys.C x.1) a b
  have ha : a = 1 := by
    unfold a CompatibilityIndicator
    simp [hxCompat]
  have hb : b = 0 := by
    unfold b CompatibilityIndicator
    simp [hxNotCompat]
  have hab : a ≠ b := by
    rw [ha, hb]
    norm_num
  refine ⟨x.1, μ, hCne, ?_, ?_⟩
  · dsimp [μ]
    exact lagBiasedSelection_pairDistribution phys x.1 a b hCne hab
  · dsimp [μ]
    exact twoStateSupport_pairDistribution phys x.1 a b

/-- Combined bridge:
lag witness + conjugacy + non-vanishing baryon charge on non-fixed C-pairs
produces a distribution with non-zero expected baryon number. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero
    {S V : Type w}
    [Fintype S] [DecidableEq S]
    (phys : ParticlePhysics S)
    (semR : _root_.PrimitiveHolonomy.Semantics P S) (obs : S → V) (target_obs : P → V)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR obs target_obs step x)]
    (hConj : LagConjugacyHypothesis (P := P) phys semR obs target_obs α step)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR obs target_obs α step)
    (hBnonfixed : ∀ s : S, phys.C s ≠ s → phys.B s ≠ 0) :
    ∃ μ : S → Rat, ExpectedB phys μ ≠ 0 := by
  rcases lagEvent_implies_lagBiasedSelection_with_nonfixed_under_conjugacy
      (P := P) phys semR obs target_obs α step hConj hLag with
    ⟨s, μ, hCs, hLagBias, hSupp⟩
  refine ⟨μ, ?_⟩
  exact expectedB_ne_zero_of_lagBiasedSelection
    (phys := phys) (μ := μ) (s := s) hCs hSupp hLagBias (hBnonfixed s hCs)

/-- In the canonical `LagState Y Int` model, non-fixed `C`-pairs automatically
have nonzero baryon charge (`B = hidden`). -/
theorem b_nonfixed_of_lagStateIntPhysics
    {Y : Type} (s : _root_.PrimitiveHolonomy.LagState Y Int) :
    (lagStateIntPhysics (Y := Y)).C s ≠ s →
    (lagStateIntPhysics (Y := Y)).B s ≠ 0 := by
  intro hC hB
  apply hC
  cases s with
  | mk vis hid =>
    dsimp [lagStateIntPhysics] at hB ⊢
    subst hB
    simp

/-- Canonical lag-to-asymmetry statement in `LagState Y Int`:
`LagEvent` + hidden-flip witness give a distribution with non-zero expected baryon number. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_hiddenFlip
    {Y : Type}
    [Fintype (_root_.PrimitiveHolonomy.LagState Y Int)]
    [DecidableEq (_root_.PrimitiveHolonomy.LagState Y Int)]
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x)]
    (hFlip : LagHiddenFlipWitness (P := P) semR target_obs α step)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step) :
    ∃ μ : _root_.PrimitiveHolonomy.LagState Y Int → Rat,
      ExpectedB (lagStateIntPhysics (Y := Y)) μ ≠ 0 := by
  have hEq :
      LagConjugacyEqHypothesis (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
        (lagStateIntPhysics (Y := Y)) semR
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step :=
    lagConjugacyEqHypothesis_lagStateInt_of_hiddenFlip (P := P) (Y := Y) semR target_obs α step hFlip
  have hConj :
      LagConjugacyHypothesis (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
        (lagStateIntPhysics (Y := Y)) semR
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step :=
    lagConjugacyHypothesis_of_eq (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
      (lagStateIntPhysics (Y := Y)) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step hEq
  exact lagEvent_implies_exists_distribution_with_expectedB_ne_zero
    (P := P) (S := _root_.PrimitiveHolonomy.LagState Y Int) (V := Y)
    (phys := lagStateIntPhysics (Y := Y))
    semR (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step
    hConj hLag (by
      intro s hs
      exact b_nonfixed_of_lagStateIntPhysics (Y := Y) s hs)

/-- Same canonical conclusion with a purely topological hidden-flip contract:
holonomy already fixes the sign relation, and `LagEvent` supplies the selection asymmetry. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_holonomyHiddenFlip
    {Y : Type}
    [Fintype (_root_.PrimitiveHolonomy.LagState Y Int)]
    [DecidableEq (_root_.PrimitiveHolonomy.LagState Y Int)]
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x)]
    (hHolFlip : HolonomyHiddenFlipWitness (P := P) semR target_obs α)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step) :
    ∃ μ : _root_.PrimitiveHolonomy.LagState Y Int → Rat,
      ExpectedB (lagStateIntPhysics (Y := Y)) μ ≠ 0 := by
  exact lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_hiddenFlip
    (P := P) (Y := Y) semR target_obs α step
    (lagHiddenFlipWitness_of_holonomyHiddenFlipWitness (P := P) (Y := Y) semR target_obs α step hHolFlip)
    hLag

/-- Same canonical conclusion from a structural semantics hypothesis:
if holonomy always flips hidden sign, then `LagEvent` yields non-zero expected baryon number. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_semanticsFlipsHiddenOnHolonomy
    {Y : Type}
    [Fintype (_root_.PrimitiveHolonomy.LagState Y Int)]
    [DecidableEq (_root_.PrimitiveHolonomy.LagState Y Int)]
    (semR : _root_.PrimitiveHolonomy.Semantics P (_root_.PrimitiveHolonomy.LagState Y Int))
    (target_obs : P → Y)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := P)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := P) semR
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x)]
    (hSemFlip : SemanticsFlipsHiddenOnHolonomy (P := P) semR target_obs)
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := P) semR
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step) :
    ∃ μ : _root_.PrimitiveHolonomy.LagState Y Int → Rat,
      ExpectedB (lagStateIntPhysics (Y := Y)) μ ≠ 0 := by
  exact lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_holonomyHiddenFlip
    (P := P) (Y := Y) semR target_obs α step
    (holonomyHiddenFlipWitness_of_semanticsFlipsHiddenOnHolonomy
      (P := P) (Y := Y) semR target_obs α hSemFlip)
    hLag

end LagSelectionBridge

-- ============================================================
-- 4.2 TOY SEMANTICS INSTANCE (explicit hidden-flip holonomy)
-- ============================================================

section ToySemanticsInstance

/-- Single-prefix toy history. -/
inductive ToyPrefix where
  | base

instance : HistoryGraph ToyPrefix where
  Path _ _ := Bool
  Deformation := by
    intro _ _ p q
    exact p ≠ q
  idPath _ := false
  compPath p q := Bool.xor p q

def toyStepFun {Y : Type} (b : Bool) :
    _root_.PrimitiveHolonomy.LagState Y Int →
      _root_.PrimitiveHolonomy.LagState Y Int
  | s =>
      if b then ⟨s.visible, -s.hidden⟩ else s

theorem toyStepFun_comp {Y : Type}
    (p q : Bool) (s : _root_.PrimitiveHolonomy.LagState Y Int) :
    toyStepFun q (toyStepFun p s) = toyStepFun (Bool.xor p q) s := by
  cases p <;> cases q <;> cases s <;> simp [toyStepFun, Bool.xor]

/-- Explicit semantics on the toy history:
`false` = identity step, `true` = hidden-sign flip step. -/
def toyLagSemantics (Y : Type) :
    _root_.PrimitiveHolonomy.Semantics ToyPrefix
      (_root_.PrimitiveHolonomy.LagState Y Int) where
  sem := by
    intro _h _k p
    exact fun s t => t = toyStepFun p s
  sem_id := by
    intro _h x y
    constructor <;> intro hxy <;> simpa [toyStepFun, _root_.PrimitiveHolonomy.relId] using hxy.symm
  sem_comp := by
    intro _h _k _l p q x z
    constructor
    · intro hz
      refine ⟨toyStepFun p x, rfl, ?_⟩
      simpa [toyStepFun_comp] using hz
    · intro hz
      rcases hz with ⟨y, hy, hz⟩
      subst hy
      simpa [toyStepFun_comp] using hz

/-- Concrete instance of the structural hidden-flip contract:
for the toy history semantics, every holonomy relation flips hidden sign. -/
theorem semanticsFlipsHiddenOnHolonomy_toyLagSemantics
    {Y : Type}
    (target_obs : ToyPrefix → Y) :
    SemanticsFlipsHiddenOnHolonomy (P := ToyPrefix)
      (Y := Y) (toyLagSemantics (Y := Y)) target_obs := by
  intro h k p q α x x' hHol
  cases h
  cases k
  rcases hHol with ⟨y, hp, hq⟩
  cases p <;> cases q
  · cases α rfl
  · have hEq : x.1 = toyStepFun true x'.1 := by
      exact hp.symm.trans hq
    have hHidden : x.1.hidden = -x'.1.hidden := by
      simpa [toyStepFun] using congrArg _root_.PrimitiveHolonomy.LagState.hidden hEq
    have hNeg : -x.1.hidden = x'.1.hidden := by
      simpa using congrArg Neg.neg hHidden
    exact hNeg.symm
  · have hEq : x'.1 = toyStepFun true x.1 := by
      exact hq.symm.trans hp
    simpa [toyStepFun] using congrArg _root_.PrimitiveHolonomy.LagState.hidden hEq
  · cases α rfl

/-- In the toy semantics instance, twisted cells force non-zero `Δ(B+L)` in the
canonical `LagState` physics (`N_f = 1` internalized). -/
theorem deltaBL_ne_zero_of_twistedOnCell_toyLagSemantics
    {Y : Type}
    (target_obs : ToyPrefix → Y)
    (φ : _root_.PrimitiveHolonomy.Gauge (P := ToyPrefix)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs)
    (c : _root_.PrimitiveHolonomy.Cell (P := ToyPrefix))
    (hTw : _root_.PrimitiveHolonomy.TwistedOnCell (P := ToyPrefix)
      (toyLagSemantics (Y := Y))
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs φ c) :
    ∃ s1 s2 : _root_.PrimitiveHolonomy.LagState Y Int,
      DeltaBL (lagStateIntPhysics (Y := Y)) s1 s2 ≠ 0 := by
  exact deltaBL_ne_zero_of_twistedOnCell_of_lagState_hidden
    (P := ToyPrefix) (Y := Y) (toyLagSemantics (Y := Y)) target_obs φ c hTw

/-- In the toy semantics instance, any lag event yields a distribution with
non-zero expected baryon number in the canonical `LagState` physics. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero_toyLagSemantics
    {Y : Type}
    [Fintype (_root_.PrimitiveHolonomy.LagState Y Int)]
    [DecidableEq (_root_.PrimitiveHolonomy.LagState Y Int)]
    (target_obs : ToyPrefix → Y)
    {h k k' : ToyPrefix} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k')
    [DecidablePred (fun x : _root_.PrimitiveHolonomy.FiberPt (P := ToyPrefix)
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs h =>
      _root_.PrimitiveHolonomy.Compatible (P := ToyPrefix) (toyLagSemantics (Y := Y))
        (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs step x)]
    (hLag : _root_.PrimitiveHolonomy.LagEvent (P := ToyPrefix) (toyLagSemantics (Y := Y))
      (_root_.PrimitiveHolonomy.lagObs (Y := Y) (B := Int)) target_obs α step) :
    ∃ μ : _root_.PrimitiveHolonomy.LagState Y Int → Rat,
      ExpectedB (lagStateIntPhysics (Y := Y)) μ ≠ 0 := by
  exact lagEvent_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_semanticsFlipsHiddenOnHolonomy
    (P := ToyPrefix) (Y := Y) (semR := toyLagSemantics (Y := Y)) target_obs α step
    (semanticsFlipsHiddenOnHolonomy_toyLagSemantics (Y := Y) target_obs)
    hLag

end ToySemanticsInstance

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
