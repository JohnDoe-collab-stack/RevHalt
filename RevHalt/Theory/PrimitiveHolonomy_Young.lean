import RevHalt.Theory.PrimitiveHolonomy_Physics
import Mathlib

/-!
# Primitive Holonomy: Young Double-Slit Layer

Constructive formalization of the core Young interference algebra:
- coherent amplitude sum (`L + R`),
- incoherent intensity (`|L|^2 + |R|^2`),
- interference term,
- decoherence/which-path interpolation.

No `noncomputable`, no `classical`.
-/

namespace PrimitiveHolonomy.Physics

universe u

/-- Two slits. -/
inductive Slit where
  | left
  | right
  deriving DecidableEq, Fintype

/-- Amplitude model on a detector space `X`. -/
structure YoungModel (X : Type u) where
  amp : Slit → X → Complex

/-- Left-slit amplitude at detector point `x`. -/
def leftAmp {X : Type u} (m : YoungModel X) (x : X) : Complex :=
  m.amp Slit.left x

/-- Right-slit amplitude at detector point `x`. -/
def rightAmp {X : Type u} (m : YoungModel X) (x : X) : Complex :=
  m.amp Slit.right x

/-- Coherent total amplitude (`A_L + A_R`). -/
def totalAmp {X : Type u} (m : YoungModel X) (x : X) : Complex :=
  leftAmp m x + rightAmp m x

/-- Coherent intensity (`|A_L + A_R|^2`). -/
def coherentIntensity {X : Type u} (m : YoungModel X) (x : X) : Real :=
  Complex.normSq (totalAmp m x)

/-- Incoherent intensity (`|A_L|^2 + |A_R|^2`). -/
def incoherentIntensity {X : Type u} (m : YoungModel X) (x : X) : Real :=
  Complex.normSq (leftAmp m x) + Complex.normSq (rightAmp m x)

/-- Interference term (`2 Re(A_L * conj(A_R))`). -/
def interferenceTerm {X : Type u} (m : YoungModel X) (x : X) : Real :=
  2 * (leftAmp m x * (starRingEnd Complex) (rightAmp m x)).re

/-- Coherent-minus-incoherent defect at detector point `x`. -/
def coherenceDefect {X : Type u} (m : YoungModel X) (x : X) : Real :=
  coherentIntensity m x - incoherentIntensity m x

/-- Young identity: coherent pattern = incoherent background + interference term. -/
theorem coherentIntensity_eq_incoherent_plus_interference {X : Type u}
    (m : YoungModel X) (x : X) :
    coherentIntensity m x = incoherentIntensity m x + interferenceTerm m x := by
  simpa [coherentIntensity, incoherentIntensity, interferenceTerm, totalAmp, leftAmp, rightAmp]
    using (Complex.normSq_add (leftAmp m x) (rightAmp m x))

/-- Decohered interpolation (which-path visibility parameter `η`). -/
def decoheredIntensity {X : Type u} (η : Real) (m : YoungModel X) (x : X) : Real :=
  incoherentIntensity m x + η * interferenceTerm m x

/-- Full which-path information (`η = 0`) kills interference. -/
theorem decoheredIntensity_zero {X : Type u}
    (m : YoungModel X) (x : X) :
    decoheredIntensity 0 m x = incoherentIntensity m x := by
  simp [decoheredIntensity]

/-- No which-path information (`η = 1`) gives back the coherent pattern. -/
theorem decoheredIntensity_one {X : Type u}
    (m : YoungModel X) (x : X) :
    decoheredIntensity 1 m x = coherentIntensity m x := by
  rw [decoheredIntensity, one_mul]
  symm
  exact coherentIntensity_eq_incoherent_plus_interference m x

/-- Coherence defect is exactly the interference term. -/
theorem coherenceDefect_eq_interferenceTerm {X : Type u}
    (m : YoungModel X) (x : X) :
    coherenceDefect m x = interferenceTerm m x := by
  unfold coherenceDefect
  linarith [coherentIntensity_eq_incoherent_plus_interference m x]

/-- Coherent and incoherent intensities coincide iff the interference term vanishes. -/
theorem coherent_eq_incoherent_iff_interference_zero {X : Type u}
    (m : YoungModel X) (x : X) :
    coherentIntensity m x = incoherentIntensity m x ↔ interferenceTerm m x = 0 := by
  constructor
  · intro hEq
    have hDef : coherenceDefect m x = 0 := by
      unfold coherenceDefect
      linarith [hEq]
    rw [coherenceDefect_eq_interferenceTerm] at hDef
    exact hDef
  · intro hI
    rw [coherentIntensity_eq_incoherent_plus_interference, hI]
    ring

/-- If `η ≠ 0`, observing decohered = incoherent implies no interference. -/
theorem interference_zero_of_decohered_eq_incoherent_of_eta_ne_zero {X : Type u}
    (η : Real) (m : YoungModel X) (x : X)
    (hη : η ≠ 0)
    (hEq : decoheredIntensity η m x = incoherentIntensity m x) :
    interferenceTerm m x = 0 := by
  unfold decoheredIntensity at hEq
  have hMul : η * interferenceTerm m x = 0 := by
    linarith [hEq]
  exact (mul_eq_zero.mp hMul).resolve_left hη

/-- If one slit is closed on `x`, the coherent and incoherent intensities coincide on `x`. -/
theorem coherent_eq_incoherent_of_leftAmp_eq_zero {X : Type u}
    (m : YoungModel X) (x : X)
    (hL : leftAmp m x = 0) :
    coherentIntensity m x = incoherentIntensity m x := by
  rw [coherentIntensity_eq_incoherent_plus_interference]
  simp [interferenceTerm, hL]

/-- Symmetric variant: right slit closed on `x`. -/
theorem coherent_eq_incoherent_of_rightAmp_eq_zero {X : Type u}
    (m : YoungModel X) (x : X)
    (hR : rightAmp m x = 0) :
    coherentIntensity m x = incoherentIntensity m x := by
  rw [coherentIntensity_eq_incoherent_plus_interference]
  simp [interferenceTerm, hR]

-- ============================================================
-- HOLONOMY-PHASE BRIDGE (explicit explanatory layer)
-- ============================================================

section HolonomyPhaseBridge

/--
Phase-coupling contract at detector point `x`:
the right-path amplitude is obtained from the left-path amplitude by a complex factor `U`.

Interpretation: `U` is the effective relative holonomy/phase between the two paths.
-/
def PhaseCoupledAt {X : Type u} (m : YoungModel X) (x : X) (U : Complex) : Prop :=
  rightAmp m x = U * leftAmp m x

/-- Under phase coupling, the interference term is controlled by `Re(U)`. -/
theorem interferenceTerm_of_phaseCoupled {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U) :
    interferenceTerm m x = 2 * U.re * Complex.normSq (leftAmp m x) := by
  unfold PhaseCoupledAt at hPhase
  rw [interferenceTerm, hPhase]
  calc
    2 * (leftAmp m x * (starRingEnd Complex) (U * leftAmp m x)).re
        = 2 * (((leftAmp m x * (starRingEnd Complex) (leftAmp m x)) *
            (starRingEnd Complex U)).re) := by
            simp [mul_left_comm, mul_comm]
    _ = 2 * ((((Complex.normSq (leftAmp m x) : ℂ) * (starRingEnd Complex U)).re)) := by
          simp [Complex.mul_conj]
    _ = 2 * (Complex.normSq (leftAmp m x) * (starRingEnd Complex U).re) := by
          simp
    _ = 2 * (Complex.normSq (leftAmp m x) * U.re) := by
          simp [Complex.conj_re]
    _ = 2 * U.re * Complex.normSq (leftAmp m x) := by ring

/-- Under phase coupling, incoherent intensity has the explicit closed form. -/
theorem incoherentIntensity_of_phaseCoupled {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U) :
    incoherentIntensity m x =
      (1 + Complex.normSq U) * Complex.normSq (leftAmp m x) := by
  unfold PhaseCoupledAt at hPhase
  rw [incoherentIntensity, hPhase, Complex.normSq_mul]
  ring

/--
Under phase coupling, coherent intensity is the sum of:
- incoherent background `(1 + |U|^2)|A_L|^2`,
- interference correction `2 Re(U)|A_L|^2`.
-/
theorem coherentIntensity_of_phaseCoupled {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U) :
    coherentIntensity m x =
      ((1 + Complex.normSq U) + 2 * U.re) * Complex.normSq (leftAmp m x) := by
  rw [coherentIntensity_eq_incoherent_plus_interference,
    incoherentIntensity_of_phaseCoupled m x U hPhase,
    interferenceTerm_of_phaseCoupled m x U hPhase]
  ring

/-- Unit-modulus phase (`|U|=1`): incoherent level is exactly `2|A_L|^2`. -/
theorem incoherentIntensity_of_phaseCoupled_unit {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1) :
    incoherentIntensity m x = (2 : Real) * Complex.normSq (leftAmp m x) := by
  rw [incoherentIntensity_of_phaseCoupled m x U hPhase, hUnit]
  ring

/-- Unit-modulus phase (`|U|=1`): coherent level is `(2 + 2 Re(U))|A_L|^2`. -/
theorem coherentIntensity_of_phaseCoupled_unit {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1) :
    coherentIntensity m x =
      (2 + 2 * U.re) * Complex.normSq (leftAmp m x) := by
  rw [coherentIntensity_of_phaseCoupled m x U hPhase, hUnit]
  ring

/-- Unit-modulus phase with purely imaginary `U` gives zero interference correction. -/
theorem coherent_eq_incoherent_of_phaseCoupled_unit_of_re_zero {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1)
    (hRe : U.re = 0) :
    coherentIntensity m x = incoherentIntensity m x := by
  rw [coherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit,
    incoherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit, hRe]
  ring

/-- Unit-modulus phase under decoherence `η`: explicit interpolation formula. -/
theorem decoheredIntensity_of_phaseCoupled_unit {X : Type u}
    (η : Real) (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1) :
    decoheredIntensity η m x =
      (2 + 2 * η * U.re) * Complex.normSq (leftAmp m x) := by
  rw [decoheredIntensity,
    incoherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit,
    interferenceTerm_of_phaseCoupled m x U hPhase]
  ring

/-- Positive relative phase projection gives constructive shift (`I_coh ≥ I_incoh`). -/
theorem incoherentIntensity_le_coherentIntensity_of_phaseCoupled_of_re_nonneg {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hRe : 0 ≤ U.re) :
    incoherentIntensity m x ≤ coherentIntensity m x := by
  rw [coherentIntensity_eq_incoherent_plus_interference,
    interferenceTerm_of_phaseCoupled m x U hPhase]
  have hNsq : 0 ≤ Complex.normSq (leftAmp m x) := Complex.normSq_nonneg _
  have hShift : 0 ≤ 2 * U.re * Complex.normSq (leftAmp m x) := by
    nlinarith
  linarith

/-- Negative relative phase projection gives destructive shift (`I_coh ≤ I_incoh`). -/
theorem coherentIntensity_le_incoherentIntensity_of_phaseCoupled_of_re_nonpos {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hRe : U.re ≤ 0) :
    coherentIntensity m x ≤ incoherentIntensity m x := by
  rw [coherentIntensity_eq_incoherent_plus_interference,
    interferenceTerm_of_phaseCoupled m x U hPhase]
  have hNsq : 0 ≤ Complex.normSq (leftAmp m x) := Complex.normSq_nonneg _
  have hShift : 2 * U.re * Complex.normSq (leftAmp m x) ≤ 0 := by
    nlinarith
  linarith

/-- For constructive shift, increasing `η` increases the detected intensity. -/
theorem decoheredIntensity_mono_eta_of_phaseCoupled_of_re_nonneg {X : Type u}
    (η1 η2 : Real) (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hRe : 0 ≤ U.re)
    (hη : η1 ≤ η2) :
    decoheredIntensity η1 m x ≤ decoheredIntensity η2 m x := by
  rw [decoheredIntensity, decoheredIntensity]
  have hNsq : 0 ≤ Complex.normSq (leftAmp m x) := Complex.normSq_nonneg _
  have hInt : 0 ≤ interferenceTerm m x := by
    rw [interferenceTerm_of_phaseCoupled m x U hPhase]
    nlinarith
  have hMul : η1 * interferenceTerm m x ≤ η2 * interferenceTerm m x :=
    mul_le_mul_of_nonneg_right hη hInt
  linarith

/-- For destructive shift, increasing `η` decreases the detected intensity. -/
theorem decoheredIntensity_antimono_eta_of_phaseCoupled_of_re_nonpos {X : Type u}
    (η1 η2 : Real) (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hRe : U.re ≤ 0)
    (hη : η1 ≤ η2) :
    decoheredIntensity η2 m x ≤ decoheredIntensity η1 m x := by
  rw [decoheredIntensity, decoheredIntensity]
  have hNsq : 0 ≤ Complex.normSq (leftAmp m x) := Complex.normSq_nonneg _
  have hInt : interferenceTerm m x ≤ 0 := by
    rw [interferenceTerm_of_phaseCoupled m x U hPhase]
    nlinarith
  have hMul : η2 * interferenceTerm m x ≤ η1 * interferenceTerm m x :=
    mul_le_mul_of_nonpos_right hη hInt
  linarith

end HolonomyPhaseBridge

-- ============================================================
-- PRIMITIVE HOLONOMY -> YOUNG OBSERVABLES (bridge contracts)
-- ============================================================

section PrimitiveHolonomyBridge

variable {P S V X : Type u} [HistoryGraph P]

/--
Bridge contract from primitive holonomy to Young amplitudes at detector point `xDet`.

Reading:
for any holonomy-related micro pair `(x, x')` on a 2-cell `α`,
there exists a unit-modulus complex factor `U` such that the two-slit amplitudes
at `xDet` are phase-coupled by `U`.
-/
def HolonomyRelInducesPhaseAt
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q) : Prop :=
  ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
    _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
      ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U

/-- Holonomy witness yields an explicit interference formula at `xDet`. -/
theorem exists_interference_formula_of_holonomyRel
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge : HolonomyRelInducesPhaseAt (P := P) sem obs target_obs m xDet α)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x') :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      interferenceTerm m xDet = 2 * U.re * Complex.normSq (leftAmp m xDet) := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, ?_⟩
  exact interferenceTerm_of_phaseCoupled m xDet U hPhase

/-- Holonomy witness yields an explicit coherent-intensity formula at `xDet`. -/
theorem exists_coherent_formula_of_holonomyRel
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge : HolonomyRelInducesPhaseAt (P := P) sem obs target_obs m xDet α)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x') :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      coherentIntensity m xDet =
        (2 + 2 * U.re) * Complex.normSq (leftAmp m xDet) := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, ?_⟩
  exact coherentIntensity_of_phaseCoupled_unit m xDet U hPhase hUnit

/-- Holonomy witness yields an explicit decohered-intensity formula at `xDet`. -/
theorem exists_decohered_formula_of_holonomyRel
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge : HolonomyRelInducesPhaseAt (P := P) sem obs target_obs m xDet α)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x') :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      decoheredIntensity η m xDet =
        (2 + 2 * η * U.re) * Complex.normSq (leftAmp m xDet) := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, ?_⟩
  exact decoheredIntensity_of_phaseCoupled_unit η m xDet U hPhase hUnit

end PrimitiveHolonomyBridge

-- ============================================================
-- CONCRETE TOY CLOSURE (bridge fully instantiated)
-- ============================================================

section ConcreteToyClosure

abbrev ToyStateInt := _root_.PrimitiveHolonomy.LagState Unit Int
abbrev toyObsUnit : ToyStateInt → Unit := _root_.PrimitiveHolonomy.lagObs (Y := Unit) (B := Int)

def toyTargetObsUnit : ToyPrefix → Unit := fun _ => ()

abbrev ToyFiberBase :=
  _root_.PrimitiveHolonomy.FiberPt (P := ToyPrefix) toyObsUnit toyTargetObsUnit ToyPrefix.base

/-- Two explicit micro-states in the base fiber (hidden `+1` and `-1`). -/
def xPlus : ToyFiberBase := ⟨⟨(), 1⟩, rfl⟩
def xMinus : ToyFiberBase := ⟨⟨(), -1⟩, rfl⟩

/-- Canonical non-trivial 2-cell in the toy history (`false ≠ true`). -/
def alphaFlip :
    HistoryGraph.Deformation (P := ToyPrefix)
      (h := ToyPrefix.base) (k := ToyPrefix.base) false true := by
  exact Bool.false_ne_true

/-- Explicit holonomy witness on the toy semantics. -/
theorem holonomyRel_xPlus_xMinus_alphaFlip :
    _root_.PrimitiveHolonomy.HolonomyRel (P := ToyPrefix)
      (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit alphaFlip xPlus xMinus := by
  refine (_root_.PrimitiveHolonomy.holonomy_def
    (P := ToyPrefix) (sem := toyLagSemantics (Y := Unit))
    (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
    alphaFlip xPlus xMinus).2 ?_
  refine ⟨xPlus, ?_, ?_⟩
  · simp [_root_.PrimitiveHolonomy.Transport, toyLagSemantics, toyStepFun, xPlus]
  · simp [_root_.PrimitiveHolonomy.Transport, toyLagSemantics, toyStepFun, xPlus, xMinus]

/-- Young model with fixed relative phase `U` and base amplitude `A`. -/
def fixedPhaseYoungModel (A U : Complex) : YoungModel Unit where
  amp
  | Slit.left, _ => A
  | Slit.right, _ => U * A

/-- In the fixed-phase model, the phase-coupling relation is definitional. -/
theorem phaseCoupledAt_fixedPhaseYoungModel (A U : Complex) (xDet : Unit) :
    PhaseCoupledAt (fixedPhaseYoungModel A U) xDet U := by
  simp [PhaseCoupledAt, fixedPhaseYoungModel, leftAmp, rightAmp]

/-- Fully concrete bridge: toy holonomy implies a unit-phase-coupled Young model. -/
theorem holonomyRelInducesPhaseAt_fixedPhaseYoungModel
    (A U : Complex) (hUnit : Complex.normSq U = 1) :
    HolonomyRelInducesPhaseAt (P := ToyPrefix) (S := ToyStateInt) (V := Unit) (X := Unit)
      (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit
      (fixedPhaseYoungModel A U) () alphaFlip := by
  intro x x' _hHol
  exact ⟨U, hUnit, phaseCoupledAt_fixedPhaseYoungModel A U ()⟩

/-- Concrete exported formula on an actual holonomy witness (no abstract bridge left). -/
theorem exists_coherent_formula_toyHolonomy_fixedPhase
    (A U : Complex) (hUnit : Complex.normSq U = 1) :
    ∃ U0 : Complex, Complex.normSq U0 = 1 ∧
      coherentIntensity (fixedPhaseYoungModel A U) () =
        (2 + 2 * U0.re) * Complex.normSq (leftAmp (fixedPhaseYoungModel A U) ()) := by
  exact exists_coherent_formula_of_holonomyRel
    (P := ToyPrefix) (S := ToyStateInt) (V := Unit) (X := Unit)
    (sem := toyLagSemantics (Y := Unit))
    (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
    (m := fixedPhaseYoungModel A U) (xDet := ())
    (α := alphaFlip)
    (holonomyRelInducesPhaseAt_fixedPhaseYoungModel A U hUnit)
    xPlus xMinus holonomyRel_xPlus_xMinus_alphaFlip

/-- Concrete constructive-interference endpoint (`U = 1`). -/
theorem coherentIntensity_toyHolonomy_inPhase (A : Complex) :
    coherentIntensity (fixedPhaseYoungModel A 1) () =
      (4 : Real) * Complex.normSq A := by
  calc
    coherentIntensity (fixedPhaseYoungModel A 1) () =
      (2 + 2) * Complex.normSq A := by
        simpa [fixedPhaseYoungModel, leftAmp] using
          (coherentIntensity_of_phaseCoupled_unit
            (m := fixedPhaseYoungModel A 1) (x := ()) (U := (1 : Complex))
            (phaseCoupledAt_fixedPhaseYoungModel A (1 : Complex) ())
            (by simp))
    _ = (4 : Real) * Complex.normSq A := by ring

/-- Concrete no-fringe endpoint (`U = i`): coherent and incoherent intensities coincide. -/
theorem coherent_eq_incoherent_toyHolonomy_quadrature (A : Complex) :
    coherentIntensity (fixedPhaseYoungModel A Complex.I) () =
      incoherentIntensity (fixedPhaseYoungModel A Complex.I) () := by
  exact coherent_eq_incoherent_of_phaseCoupled_unit_of_re_zero
    (m := fixedPhaseYoungModel A Complex.I) (x := ()) (U := Complex.I)
    (phaseCoupledAt_fixedPhaseYoungModel A Complex.I ())
    Complex.normSq_I Complex.I_re

-- ============================================================
-- ANGLE PARAMETRIZATION (explicit fringe formulas)
-- ============================================================

/-- The angle phase `⟨cos θ, sin θ⟩` always has modulus 1. -/
theorem normSq_phase_of_angle (θ : Real) :
    Complex.normSq (⟨Real.cos θ, Real.sin θ⟩ : Complex) = 1 := by
  have h := Real.cos_sq_add_sin_sq θ
  simpa [Complex.normSq, pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm,
    add_left_comm, add_assoc] using h

/-- Angle form of the interference term on the fixed-phase model: `2 cos(θ) |A|^2`. -/
theorem interferenceTerm_fixedPhaseYoungModel_of_angle (A : Complex) (θ : Real) :
    interferenceTerm (fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex)) () =
      2 * Real.cos θ * Complex.normSq A := by
  simpa [fixedPhaseYoungModel, leftAmp] using
    (interferenceTerm_of_phaseCoupled
      (m := fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (x := ()) (U := (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (phaseCoupledAt_fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex) ()))

/-- Angle form of coherent intensity on the fixed-phase model: `(2 + 2 cos(θ)) |A|^2`. -/
theorem coherentIntensity_fixedPhaseYoungModel_of_angle (A : Complex) (θ : Real) :
    coherentIntensity (fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex)) () =
      (2 + 2 * Real.cos θ) * Complex.normSq A := by
  simpa [fixedPhaseYoungModel, leftAmp] using
    (coherentIntensity_of_phaseCoupled_unit
      (m := fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (x := ()) (U := (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (phaseCoupledAt_fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex) ())
      (normSq_phase_of_angle θ))

/-- Angle form of decohered intensity on the fixed-phase model: `(2 + 2η cos(θ)) |A|^2`. -/
theorem decoheredIntensity_fixedPhaseYoungModel_of_angle (η : Real) (A : Complex) (θ : Real) :
    decoheredIntensity η (fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex)) () =
      (2 + 2 * η * Real.cos θ) * Complex.normSq A := by
  simpa [fixedPhaseYoungModel, leftAmp] using
    (decoheredIntensity_of_phaseCoupled_unit
      (η := η) (m := fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (x := ()) (U := (⟨Real.cos θ, Real.sin θ⟩ : Complex))
      (phaseCoupledAt_fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex) ())
      (normSq_phase_of_angle θ))

/-- Physical envelope for coherent intensity in the angle parametrization (`0 ≤ I ≤ 4|A|^2`). -/
theorem coherentIntensity_fixedPhaseYoungModel_bounds_of_angle (A : Complex) (θ : Real) :
    0 ≤ coherentIntensity (fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex)) () ∧
      coherentIntensity (fixedPhaseYoungModel A (⟨Real.cos θ, Real.sin θ⟩ : Complex)) () ≤
        (4 : Real) * Complex.normSq A := by
  rw [coherentIntensity_fixedPhaseYoungModel_of_angle]
  have hCosLo : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hCosHi : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hA : 0 ≤ Complex.normSq A := Complex.normSq_nonneg A
  constructor
  · have hCoef : 0 ≤ 2 + 2 * Real.cos θ := by nlinarith
    exact mul_nonneg hCoef hA
  · have hCoefLe : 2 + 2 * Real.cos θ ≤ 4 := by nlinarith
    have hMul : (2 + 2 * Real.cos θ) * Complex.normSq A ≤ 4 * Complex.normSq A :=
      mul_le_mul_of_nonneg_right hCoefLe hA
    simpa using hMul

/-- Angle endpoint `θ = 0`: fully constructive interference. -/
theorem coherentIntensity_fixedPhaseYoungModel_zero_angle (A : Complex) :
    coherentIntensity (fixedPhaseYoungModel A (⟨Real.cos 0, Real.sin 0⟩ : Complex)) () =
      (4 : Real) * Complex.normSq A := by
  rw [coherentIntensity_fixedPhaseYoungModel_of_angle, Real.cos_zero]
  ring

/-- Angle endpoint `θ = π`: fully destructive interference. -/
theorem coherentIntensity_fixedPhaseYoungModel_pi_angle (A : Complex) :
    coherentIntensity (fixedPhaseYoungModel A (⟨Real.cos Real.pi, Real.sin Real.pi⟩ : Complex)) () = 0 := by
  rw [coherentIntensity_fixedPhaseYoungModel_of_angle, Real.cos_pi]
  ring

end ConcreteToyClosure

section Regimes

/-- In-phase regime (`A_R = A_L`): total amplitude is `2 * A_L`. -/
theorem totalAmp_eq_two_mul_of_inPhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    totalAmp m x = (2 : Complex) * leftAmp m x := by
  simp [totalAmp, hEq, two_mul]

/-- In-phase regime: coherent intensity is `4 |A_L|^2`. -/
theorem coherentIntensity_of_inPhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    coherentIntensity m x = (4 : Real) * Complex.normSq (leftAmp m x) := by
  rw [coherentIntensity, totalAmp_eq_two_mul_of_inPhase m x hEq]
  calc
    Complex.normSq ((2 : Complex) * leftAmp m x)
        = Complex.normSq (2 : Complex) * Complex.normSq (leftAmp m x) := by
            simp [Complex.normSq_mul]
    _ = (4 : Real) * Complex.normSq (leftAmp m x) := by
          norm_num [Complex.normSq_natCast]

/-- In-phase regime: incoherent intensity is `2 |A_L|^2`. -/
theorem incoherentIntensity_of_inPhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    incoherentIntensity m x = (2 : Real) * Complex.normSq (leftAmp m x) := by
  simp [incoherentIntensity, hEq, two_mul]

/-- In-phase regime: interference term is `2 |A_L|^2`. -/
theorem interferenceTerm_of_inPhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    interferenceTerm m x = (2 : Real) * Complex.normSq (leftAmp m x) := by
  simp [interferenceTerm, hEq, Complex.normSq]

/-- Opposite-phase regime (`A_R = -A_L`): coherent intensity vanishes. -/
theorem coherentIntensity_zero_of_oppositePhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    coherentIntensity m x = 0 := by
  simp [coherentIntensity, totalAmp, hOpp]

/-- Opposite-phase regime: incoherent intensity is `2 |A_L|^2`. -/
theorem incoherentIntensity_of_oppositePhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    incoherentIntensity m x = (2 : Real) * Complex.normSq (leftAmp m x) := by
  simp [incoherentIntensity, hOpp, two_mul]

/-- Opposite-phase regime: interference term is `-2 |A_L|^2`. -/
theorem interferenceTerm_of_oppositePhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    interferenceTerm m x = -((2 : Real) * Complex.normSq (leftAmp m x)) := by
  simp [interferenceTerm, hOpp, Complex.normSq]
  ring

/-- In-phase regime, fully exhibited:
coherent / incoherent / interference all as explicit multiples of `|A_L|^2`. -/
theorem exhibition_of_inPhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    coherentIntensity m x = (4 : Real) * Complex.normSq (leftAmp m x) ∧
    incoherentIntensity m x = (2 : Real) * Complex.normSq (leftAmp m x) ∧
    interferenceTerm m x = (2 : Real) * Complex.normSq (leftAmp m x) := by
  refine ⟨coherentIntensity_of_inPhase m x hEq, ?_⟩
  refine ⟨incoherentIntensity_of_inPhase m x hEq, ?_⟩
  exact interferenceTerm_of_inPhase m x hEq

/-- Opposite-phase regime, fully exhibited:
destructive interference (`I_coh = 0`) and negative interference term. -/
theorem exhibition_of_oppositePhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    coherentIntensity m x = 0 ∧
    incoherentIntensity m x = (2 : Real) * Complex.normSq (leftAmp m x) ∧
    interferenceTerm m x = -((2 : Real) * Complex.normSq (leftAmp m x)) := by
  refine ⟨coherentIntensity_zero_of_oppositePhase m x hOpp, ?_⟩
  refine ⟨incoherentIntensity_of_oppositePhase m x hOpp, ?_⟩
  exact interferenceTerm_of_oppositePhase m x hOpp

/-- In-phase regime under decoherence parameter `η`:
`I_η = (2 + 2η) |A_L|^2`. -/
theorem decoheredIntensity_of_inPhase {X : Type u}
    (η : Real) (m : YoungModel X) (x : X)
    (hEq : rightAmp m x = leftAmp m x) :
    decoheredIntensity η m x =
      ((2 : Real) + 2 * η) * Complex.normSq (leftAmp m x) := by
  rw [decoheredIntensity, incoherentIntensity_of_inPhase m x hEq, interferenceTerm_of_inPhase m x hEq]
  ring

/-- Opposite-phase regime under decoherence parameter `η`:
`I_η = (2 - 2η) |A_L|^2`. -/
theorem decoheredIntensity_of_oppositePhase {X : Type u}
    (η : Real) (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    decoheredIntensity η m x =
      ((2 : Real) - 2 * η) * Complex.normSq (leftAmp m x) := by
  rw [decoheredIntensity, incoherentIntensity_of_oppositePhase m x hOpp,
    interferenceTerm_of_oppositePhase m x hOpp]
  ring

end Regimes

end PrimitiveHolonomy.Physics
