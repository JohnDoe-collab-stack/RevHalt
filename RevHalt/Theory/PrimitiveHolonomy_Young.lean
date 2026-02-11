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

/-- Decoherence shift from coherent intensity: `(η - 1)` times interference. -/
theorem decohered_minus_coherent_eq_eta_sub_one_mul_interference {X : Type u}
    (η : Real) (m : YoungModel X) (x : X) :
    decoheredIntensity η m x - coherentIntensity m x =
      (η - 1) * interferenceTerm m x := by
  rw [decoheredIntensity, coherentIntensity_eq_incoherent_plus_interference]
  ring

/-- Decoherence gap to incoherent intensity: `-η` times interference. -/
theorem incoherent_minus_decohered_eq_neg_eta_mul_interference {X : Type u}
    (η : Real) (m : YoungModel X) (x : X) :
    incoherentIntensity m x - decoheredIntensity η m x =
      (-η) * interferenceTerm m x := by
  rw [decoheredIntensity]
  ring

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

/-- The quotient phase `A_R / A_L` satisfies phase coupling when `A_L ≠ 0`. -/
theorem phaseCoupledAt_of_div {X : Type u}
    (m : YoungModel X) (x : X)
    (hL : leftAmp m x ≠ 0) :
    PhaseCoupledAt m x (rightAmp m x / leftAmp m x) := by
  unfold PhaseCoupledAt
  have hMul : (rightAmp m x / leftAmp m x) * leftAmp m x = rightAmp m x := by
    field_simp [hL]
  exact hMul.symm

/-- If `A_L ≠ 0`, the phase-coupling factor at `x` is unique. -/
theorem phaseCoupledAt_unique_of_leftAmp_ne_zero {X : Type u}
    (m : YoungModel X) (x : X) (U U' : Complex)
    (hL : leftAmp m x ≠ 0)
    (hU : PhaseCoupledAt m x U)
    (hU' : PhaseCoupledAt m x U') :
    U = U' := by
  unfold PhaseCoupledAt at hU hU'
  have hMul : (U - U') * leftAmp m x = 0 := by
    calc
      (U - U') * leftAmp m x = U * leftAmp m x - U' * leftAmp m x := by ring
      _ = rightAmp m x - rightAmp m x := by rw [← hU, ← hU']
      _ = 0 := by ring
  have hDiff : U - U' = 0 := (mul_eq_zero.mp hMul).resolve_right hL
  exact sub_eq_zero.mp hDiff

/-- If left/right amplitudes have equal norm and left is nonzero, `A_R / A_L` is unit-modulus. -/
theorem normSq_div_eq_one_of_normSq_eq {X : Type u}
    (m : YoungModel X) (x : X)
    (hL : leftAmp m x ≠ 0)
    (hNorm : Complex.normSq (rightAmp m x) = Complex.normSq (leftAmp m x)) :
    Complex.normSq (rightAmp m x / leftAmp m x) = 1 := by
  rw [Complex.normSq_div, hNorm]
  have hNsq : Complex.normSq (leftAmp m x) ≠ 0 := by
    intro h0
    exact hL ((Complex.normSq_eq_zero).1 h0)
  exact div_self hNsq

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

/-- Unit-modulus phase with `Re(U) = -1` gives a dark fringe (`I_coh = 0`). -/
theorem coherentIntensity_zero_of_phaseCoupled_unit_of_re_eq_neg_one {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1)
    (hRe : U.re = -1) :
    coherentIntensity m x = 0 := by
  rw [coherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit, hRe]
  ring

/-- Under unit phase coupling and `A_L ≠ 0`, dark fringe is equivalent to `Re(U) = -1`. -/
theorem coherentIntensity_zero_iff_re_eq_neg_one_of_phaseCoupled_unit_of_leftAmp_ne_zero
    {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1)
    (hL : leftAmp m x ≠ 0) :
    coherentIntensity m x = 0 ↔ U.re = -1 := by
  rw [coherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit]
  have hNsq : Complex.normSq (leftAmp m x) ≠ 0 := by
    intro h0
    exact hL ((Complex.normSq_eq_zero).1 h0)
  constructor
  · intro hZero
    have hCoef : 2 + 2 * U.re = 0 := (mul_eq_zero.mp hZero).resolve_right hNsq
    linarith
  · intro hRe
    rw [hRe]
    ring

/-- In dark-fringe phase (`Re(U) = -1`), the interference term is `-2|A_L|^2`. -/
theorem interferenceTerm_of_phaseCoupled_of_re_eq_neg_one {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hRe : U.re = -1) :
    interferenceTerm m x = -((2 : Real) * Complex.normSq (leftAmp m x)) := by
  rw [interferenceTerm_of_phaseCoupled m x U hPhase, hRe]
  ring

/-- In dark-fringe phase (`Re(U) = -1`), the coherent deficit is exactly `2|A_L|^2`. -/
theorem incoherentIntensity_sub_coherentIntensity_of_phaseCoupled_unit_of_re_eq_neg_one {X : Type u}
    (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1)
    (hRe : U.re = -1) :
    incoherentIntensity m x - coherentIntensity m x =
      (2 : Real) * Complex.normSq (leftAmp m x) := by
  rw [incoherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit,
    coherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit, hRe]
  ring

/-- In dark-fringe phase (`Re(U) = -1`), decoherence gap is exactly `2η|A_L|^2`. -/
theorem incoherentIntensity_sub_decoheredIntensity_of_phaseCoupled_unit_of_re_eq_neg_one {X : Type u}
    (η : Real) (m : YoungModel X) (x : X) (U : Complex)
    (hPhase : PhaseCoupledAt m x U)
    (hUnit : Complex.normSq U = 1)
    (hRe : U.re = -1) :
    incoherentIntensity m x - decoheredIntensity η m x =
      (2 * η) * Complex.normSq (leftAmp m x) := by
  rw [decoheredIntensity,
    incoherentIntensity_of_phaseCoupled_unit m x U hPhase hUnit,
    interferenceTerm_of_phaseCoupled m x U hPhase, hRe]
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

/-- Holonomy witness yields an explicit interference formula at `xDet`. -/
theorem exists_interference_formula_of_holonomyRel
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
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
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x') :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      coherentIntensity m xDet =
        (2 + 2 * U.re) * Complex.normSq (leftAmp m xDet) := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, ?_⟩
  exact coherentIntensity_of_phaseCoupled_unit m xDet U hPhase hUnit

/-- For nonzero left amplitude, a dark fringe forces `Re(U) = -1` on the induced unit phase. -/
theorem exists_phase_re_eq_neg_one_of_coherent_zero_of_holonomyRel_of_leftAmp_ne_zero
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (hZero : coherentIntensity m xDet = 0)
    (hL : leftAmp m xDet ≠ 0) :
    ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U ∧ U.re = -1 := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, hPhase, ?_⟩
  exact (coherentIntensity_zero_iff_re_eq_neg_one_of_phaseCoupled_unit_of_leftAmp_ne_zero
    (m := m) (x := xDet) (U := U) hPhase hUnit hL).1 hZero

/-- On a fixed holonomy witness with `A_L ≠ 0`, dark fringe is equivalent to `Re(U) = -1`
for some induced unit phase witness. -/
theorem coherent_zero_iff_exists_phase_re_eq_neg_one_of_holonomyRel_of_leftAmp_ne_zero
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (hL : leftAmp m xDet ≠ 0) :
    coherentIntensity m xDet = 0 ↔
      ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U ∧ U.re = -1 := by
  constructor
  · intro hZero
    exact exists_phase_re_eq_neg_one_of_coherent_zero_of_holonomyRel_of_leftAmp_ne_zero
      sem obs target_obs m xDet α hBridge x x' hHol hZero hL
  · intro hPhaseNeg
    rcases hPhaseNeg with ⟨U, hUnit, hPhase, hRe⟩
    exact coherentIntensity_zero_of_phaseCoupled_unit_of_re_eq_neg_one
      (m := m) (x := xDet) (U := U) hPhase hUnit hRe

/-- On a dark-fringe holonomy witness (`A_L ≠ 0`), decoherence gap is exactly `2η|A_L|^2`. -/
theorem exists_incoherent_sub_decohered_formula_of_holonomyRel_of_coherent_zero_of_leftAmp_ne_zero
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (hZero : coherentIntensity m xDet = 0)
    (hL : leftAmp m xDet ≠ 0) :
    ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U ∧ U.re = -1 ∧
      incoherentIntensity m xDet - decoheredIntensity η m xDet =
        (2 * η) * Complex.normSq (leftAmp m xDet) := by
  rcases exists_phase_re_eq_neg_one_of_coherent_zero_of_holonomyRel_of_leftAmp_ne_zero
      sem obs target_obs m xDet α hBridge x x' hHol hZero hL with
      ⟨U, hUnit, hPhase, hRe⟩
  refine ⟨U, hUnit, hPhase, hRe, ?_⟩
  exact incoherentIntensity_sub_decoheredIntensity_of_phaseCoupled_unit_of_re_eq_neg_one
    η m xDet U hPhase hUnit hRe

/-- Holonomy witness yields an explicit decohered-intensity formula at `xDet`. -/
theorem exists_decohered_formula_of_holonomyRel
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (m : YoungModel X) (xDet : X)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hBridge :
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x') :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      decoheredIntensity η m xDet =
        (2 + 2 * η * U.re) * Complex.normSq (leftAmp m xDet) := by
  rcases hBridge x x' hHol with ⟨U, hUnit, hPhase⟩
  refine ⟨U, hUnit, ?_⟩
  exact decoheredIntensity_of_phaseCoupled_unit η m xDet U hPhase hUnit

/--
If every corrected holonomy witness projects to a bare holonomy witness, and bare holonomy
at `xDet` enforces a dark fringe, then each admissible obstruction witness yields a unit phase
with `Re(U) = -1`.
-/
theorem exists_phase_re_eq_neg_one_per_admissibleGauge_of_obstructionWrt
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (m : YoungModel X) (xDet : X)
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) sem obs target_obs OK J)
    (hProj :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.CorrectedHolonomy (P := P) sem obs target_obs φ α x x' →
          _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (hBridge : ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q),
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (hDark : ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        coherentIntensity m xDet = 0)
    (hL : leftAmp m xDet ≠ 0) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
      ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U ∧ U.re = -1 := by
  intro φ hOK
  rcases ((_root_.PrimitiveHolonomy.obstructionWrt_iff_twistedOnCell
      (P := P) sem obs target_obs OK J).1 hObs) φ hOK with ⟨c, _hcJ, hTw⟩
  rcases c with ⟨h, k, p, q, ⟨α⟩⟩
  rcases hTw with ⟨x, x', _hxNe, hCorr⟩
  have hHol :
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' :=
    hProj α φ x x' hCorr
  have hZero : coherentIntensity m xDet = 0 := hDark α x x' hHol
  rcases exists_phase_re_eq_neg_one_of_coherent_zero_of_holonomyRel_of_leftAmp_ne_zero
      (P := P) (S := S) (V := V) (X := X)
      sem obs target_obs m xDet α (hBridge α) x x' hHol hZero hL with
      ⟨U, hUnit, hPhase, hRe⟩
  exact ⟨U, hUnit, hPhase, hRe⟩

/--
Under the same projection and dark-fringe contracts, each admissible obstruction witness yields
the exact decoherence gap formula `I_incoh - I_η = 2η |A_L|^2` at `xDet`.
-/
theorem exists_incoherent_sub_decohered_formula_per_admissibleGauge_of_obstructionWrt
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (obs : S → V) (target_obs : P → V)
    (OK : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs → Prop)
    (J : Set (_root_.PrimitiveHolonomy.Cell (P := P)))
    (m : YoungModel X) (xDet : X)
    (hObs : _root_.PrimitiveHolonomy.ObstructionWrt (P := P) sem obs target_obs OK J)
    (hProj :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.CorrectedHolonomy (P := P) sem obs target_obs φ α x x' →
          _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (hBridge : ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q),
      ∀ x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h,
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
          ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U)
    (hDark : ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        coherentIntensity m xDet = 0)
    (hL : leftAmp m xDet ≠ 0) :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := P) obs target_obs, OK φ →
      ∃ U : Complex, Complex.normSq U = 1 ∧ PhaseCoupledAt m xDet U ∧ U.re = -1 ∧
        incoherentIntensity m xDet - decoheredIntensity η m xDet =
          (2 * η) * Complex.normSq (leftAmp m xDet) := by
  intro φ hOK
  rcases exists_phase_re_eq_neg_one_per_admissibleGauge_of_obstructionWrt
      (P := P) (S := S) (V := V) (X := X)
      sem obs target_obs OK J m xDet hObs hProj hBridge hDark hL φ hOK with
      ⟨U, hUnit, hPhase, hRe⟩
  refine ⟨U, hUnit, hPhase, hRe, ?_⟩
  exact incoherentIntensity_sub_decoheredIntensity_of_phaseCoupled_unit_of_re_eq_neg_one
    η m xDet U hPhase hUnit hRe

end PrimitiveHolonomyBridge

-- ============================================================
-- DERIVED PHASE FROM WEIGHTED SEMANTICS (non-axiomatic U)
-- ============================================================

section DerivedPhaseFromWeightedSemantics

variable {P S V : Type u} [HistoryGraph P]

/-- Two-path Young model extracted from a complex weighted semantics and a fixed source state. -/
def youngModelOfTwoPaths
    (semW : WeightedSemantics (P := P) S Complex)
    {h k : P} (p q : HistoryGraph.Path h k) (sSrc : S) : YoungModel S where
  amp slit sDet :=
    match slit with
    | Slit.left => semW.sem p sSrc sDet
    | Slit.right => semW.sem q sSrc sDet

/--
Minimal primitive bridge data on holonomy witnesses:
for each witness `(α, x, x', hHol)` and detector state `sDet`, we assume only:
1) right amplitude factorizes through a phase field,
2) left/right amplitudes have equal norm.

No separate unit-modulus axiom on the phase field is postulated.
-/
def SemanticsPhaseHypothesisOnHolonomy
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (phase :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        S → Complex) : Prop :=
  ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x'),
    ∀ sDet : S,
      semW.sem q x.1 sDet = phase α x x' hHol sDet * semW.sem p x.1 sDet ∧
      Complex.normSq (semW.sem q x.1 sDet) = Complex.normSq (semW.sem p x.1 sDet)

/--
From the minimal primitive bridge data (factorization + norm balance), the unit-phase
bridge is derived. The unit modulus of the coupling phase is proved, not assumed.
-/
theorem semanticsDerivedUnitPhaseOnHolonomy_of_phaseHypothesis
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (phase :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        S → Complex)
    (hPrim : SemanticsPhaseHypothesisOnHolonomy
      (P := P) (S := S) (V := V) sem semW obs target_obs phase) :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
      ∀ sDet : S, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  intro h k p q α x x' hHol sDet
  let m : YoungModel S := youngModelOfTwoPaths (P := P) semW p q x.1
  by_cases hL : leftAmp m sDet = 0
  · have hBal :
      Complex.normSq (rightAmp m sDet) = Complex.normSq (leftAmp m sDet) := by
      simpa [m, rightAmp, leftAmp, youngModelOfTwoPaths] using (hPrim α x x' hHol sDet).2
    have hRnormZero : Complex.normSq (rightAmp m sDet) = 0 := by
      simpa [hL] using hBal
    have hR : rightAmp m sDet = 0 := (Complex.normSq_eq_zero).1 hRnormZero
    refine ⟨(1 : Complex), by simp, ?_⟩
    unfold PhaseCoupledAt
    simp [m, hL, hR]
  · have hFact :
      rightAmp m sDet = phase α x x' hHol sDet * leftAmp m sDet := by
      simpa [m, rightAmp, leftAmp, youngModelOfTwoPaths, mul_comm] using (hPrim α x x' hHol sDet).1
    have hBal :
      Complex.normSq (rightAmp m sDet) = Complex.normSq (leftAmp m sDet) := by
      simpa [m, rightAmp, leftAmp, youngModelOfTwoPaths] using (hPrim α x x' hHol sDet).2
    have hNormMul :
        Complex.normSq (phase α x x' hHol sDet) * Complex.normSq (leftAmp m sDet) =
          Complex.normSq (leftAmp m sDet) := by
      calc
        Complex.normSq (phase α x x' hHol sDet) * Complex.normSq (leftAmp m sDet)
            = Complex.normSq (phase α x x' hHol sDet * leftAmp m sDet) := by
                simp [Complex.normSq_mul]
        _ = Complex.normSq (rightAmp m sDet) := by simp [hFact]
        _ = Complex.normSq (leftAmp m sDet) := hBal
    have hLeftNormNe : Complex.normSq (leftAmp m sDet) ≠ 0 := by
      intro h0
      exact hL ((Complex.normSq_eq_zero).1 h0)
    have hLeftNormPos : 0 < Complex.normSq (leftAmp m sDet) :=
      lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hLeftNormNe)
    have hUnit : Complex.normSq (phase α x x' hHol sDet) = 1 := by
      nlinarith [hNormMul, hLeftNormPos]
    refine ⟨phase α x x' hHol sDet, hUnit, ?_⟩
    simpa [m] using hFact

/-- Ratio-unitary contract implies the existential unit-phase bridge. -/
theorem semanticsDerivedUnitPhaseOnHolonomy_of_ratioUnitary
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hRatio :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S,
          leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet ≠ 0 ∧
          Complex.normSq (rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) =
            Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet)) :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
      ∀ sDet : S, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  intro h k p q α x x' hHol sDet
  rcases hRatio α x x' hHol sDet with ⟨hL, hNorm⟩
  refine ⟨rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet /
      leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet, ?_, ?_⟩
  · exact normSq_div_eq_one_of_normSq_eq
      (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL hNorm
  · exact phaseCoupledAt_of_div
      (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL

/-- Under the ratio-unitary contract, any coupled phase equals the forced ratio `A_R / A_L`. -/
theorem phase_eq_div_of_ratioUnitary
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hRatio :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S,
          leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet ≠ 0 ∧
          Complex.normSq (rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) =
            Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet))
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) (U : Complex)
    (hCoupled : PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U) :
    U = rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet /
      leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet := by
  rcases hRatio α x x' hHol sDet with ⟨hL, _hNorm⟩
  exact phaseCoupledAt_unique_of_leftAmp_ne_zero
    (m := youngModelOfTwoPaths (P := P) semW p q x.1)
    (x := sDet)
    (U := U)
    (U' := rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet /
      leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet)
    hL
    hCoupled
    (phaseCoupledAt_of_div
      (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL)

/-- Under the ratio-unitary contract, unit phase coupling exists uniquely. -/
theorem existsUnique_unitPhaseCoupling_of_holonomyRel_of_ratioUnitary
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hRatio :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S,
          leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet ≠ 0 ∧
          Complex.normSq (rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) =
            Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet))
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃! U : Complex,
      Complex.normSq U = 1 ∧
      PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  rcases hRatio α x x' hHol sDet with ⟨hL, hNorm⟩
  refine ⟨rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet /
      leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact normSq_div_eq_one_of_normSq_eq
        (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL hNorm
    · exact phaseCoupledAt_of_div
        (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL
  · intro U hU
    exact phaseCoupledAt_unique_of_leftAmp_ne_zero
      (m := youngModelOfTwoPaths (P := P) semW p q x.1)
      (x := sDet)
      (U := U)
      (U' := rightAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet /
        leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet)
      hL
      hU.2
      (phaseCoupledAt_of_div
        (m := youngModelOfTwoPaths (P := P) semW p q x.1) (x := sDet) hL)

/--
Complete holonomic phase data:
`phase` is an explicit map from full holonomy data `(α, x, x', hHol, sDet)` to a coupling phase.
-/
structure CompleteHolonomyPhaseData
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V) where
  phase :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
      S → Complex
  phase_unit :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
      (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
      (sDet : S),
      Complex.normSq (phase α x x' hHol sDet) = 1
  phase_coupled :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
      (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
      (sDet : S),
      PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet
        (phase α x x' hHol sDet)

/-- Complete holonomic phase data induces the existential bridge contract. -/
theorem semanticsDerivedUnitPhaseOnHolonomy_of_completeHolonomyPhaseData
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hData : CompleteHolonomyPhaseData (P := P) sem semW obs target_obs) :
    ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
      _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
      ∀ sDet : S, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  intro h k p q α x x' hHol sDet
  refine ⟨hData.phase α x x' hHol sDet, ?_, ?_⟩
  · exact hData.phase_unit α x x' hHol sDet
  · exact hData.phase_coupled α x x' hHol sDet

/-- Coherent formula with explicit phase computed from complete holonomic data. -/
theorem coherentIntensity_formula_of_holonomyRel_of_completeHolonomyPhaseData
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hData : CompleteHolonomyPhaseData (P := P) sem semW obs target_obs)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    coherentIntensity (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
      (2 + 2 * (hData.phase α x x' hHol sDet).re) *
        Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  exact coherentIntensity_of_phaseCoupled_unit
    (m := youngModelOfTwoPaths (P := P) semW p q x.1)
    (x := sDet)
    (U := hData.phase α x x' hHol sDet)
    (hData.phase_coupled α x x' hHol sDet)
    (hData.phase_unit α x x' hHol sDet)

/-- Decohered formula with explicit phase computed from complete holonomic data. -/
theorem decoheredIntensity_formula_of_holonomyRel_of_completeHolonomyPhaseData
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (hData : CompleteHolonomyPhaseData (P := P) sem semW obs target_obs)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    decoheredIntensity η (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
      (2 + 2 * η * (hData.phase α x x' hHol sDet).re) *
        Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  exact decoheredIntensity_of_phaseCoupled_unit
    (η := η)
    (m := youngModelOfTwoPaths (P := P) semW p q x.1)
    (x := sDet)
    (U := hData.phase α x x' hHol sDet)
    (hData.phase_coupled α x x' hHol sDet)
    (hData.phase_unit α x x' hHol sDet)

/-- For a holonomy witness, unit-phase coupling now depends on `(α, x, x', sDet)`. -/
theorem exists_unitPhaseCoupling_of_holonomyRel
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hDerived :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S, ∃ U : Complex,
          Complex.normSq U = 1 ∧
          PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  exact hDerived α x x' hHol sDet

/-- Legacy name kept for compatibility. -/
theorem exists_unitPhaseCoupling_of_holonomyRel_of_leftAmp_ne_zero
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hDerived :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S, ∃ U : Complex,
          Complex.normSq U = 1 ∧
          PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  exact exists_unitPhaseCoupling_of_holonomyRel
    (P := P) (S := S) (V := V)
    sem semW obs target_obs α hDerived x x' hHol sDet

/-- Coherent intensity formula from a holonomy witness, with semantics-derived unit phase. -/
theorem exists_coherentIntensity_formula_of_holonomyRel
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hDerived :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S, ∃ U : Complex,
          Complex.normSq U = 1 ∧
          PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      coherentIntensity (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
        (2 + 2 * U.re) *
          Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  rcases hDerived α x x' hHol sDet with ⟨U, hUnit, hCoupled⟩
  refine ⟨U, hUnit, ?_⟩
  exact coherentIntensity_of_phaseCoupled_unit
    (m := youngModelOfTwoPaths (P := P) semW p q x.1)
    (x := sDet)
    (U := U)
    hCoupled
    hUnit

/-- Decohered intensity formula from a holonomy witness, with semantics-derived unit phase. -/
theorem exists_decoheredIntensity_formula_of_holonomyRel
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (hDerived :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        ∀ sDet : S, ∃ U : Complex,
          Complex.normSq U = 1 ∧
          PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      decoheredIntensity η (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
        (2 + 2 * η * U.re) *
          Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  rcases hDerived α x x' hHol sDet with ⟨U, hUnit, hCoupled⟩
  refine ⟨U, hUnit, ?_⟩
  exact decoheredIntensity_of_phaseCoupled_unit
    (η := η)
    (m := youngModelOfTwoPaths (P := P) semW p q x.1)
    (x := sDet)
    (U := U)
    hCoupled
    hUnit

/--
Direct bridge from the minimal primitive complex-semantics assumptions:
factorization + norm balance imply unit phase coupling on each holonomy witness.
-/
theorem exists_unitPhaseCoupling_of_holonomyRel_of_phaseHypothesis
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (phase :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        S → Complex)
    (hPrim : SemanticsPhaseHypothesisOnHolonomy
      (P := P) (S := S) (V := V) sem semW obs target_obs phase)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      PhaseCoupledAt (youngModelOfTwoPaths (P := P) semW p q x.1) sDet U := by
  exact exists_unitPhaseCoupling_of_holonomyRel
    (P := P) (S := S) (V := V)
    sem semW obs target_obs α
    (semanticsDerivedUnitPhaseOnHolonomy_of_phaseHypothesis
      (P := P) (S := S) (V := V)
      sem semW obs target_obs phase hPrim)
    x x' hHol sDet

/--
Direct coherent-intensity formula from the minimal primitive complex-semantics assumptions.
-/
theorem exists_coherentIntensity_formula_of_holonomyRel_of_phaseHypothesis
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (phase :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        S → Complex)
    (hPrim : SemanticsPhaseHypothesisOnHolonomy
      (P := P) (S := S) (V := V) sem semW obs target_obs phase)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      coherentIntensity (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
        (2 + 2 * U.re) *
          Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  exact exists_coherentIntensity_formula_of_holonomyRel
    (P := P) (S := S) (V := V)
    sem semW obs target_obs α
    (semanticsDerivedUnitPhaseOnHolonomy_of_phaseHypothesis
      (P := P) (S := S) (V := V)
      sem semW obs target_obs phase hPrim)
    x x' hHol sDet

/--
Direct decohered-intensity formula from the minimal primitive complex-semantics assumptions.
-/
theorem exists_decoheredIntensity_formula_of_holonomyRel_of_phaseHypothesis
    (η : Real)
    (sem : _root_.PrimitiveHolonomy.Semantics P S)
    (semW : WeightedSemantics (P := P) S Complex)
    (obs : S → V) (target_obs : P → V)
    (phase :
      ∀ {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
        (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h),
        _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x' →
        S → Complex)
    (hPrim : SemanticsPhaseHypothesisOnHolonomy
      (P := P) (S := S) (V := V) sem semW obs target_obs phase)
    {h k : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (x x' : _root_.PrimitiveHolonomy.FiberPt (P := P) obs target_obs h)
    (hHol : _root_.PrimitiveHolonomy.HolonomyRel (P := P) sem obs target_obs α x x')
    (sDet : S) :
    ∃ U : Complex, Complex.normSq U = 1 ∧
      decoheredIntensity η (youngModelOfTwoPaths (P := P) semW p q x.1) sDet =
        (2 + 2 * η * U.re) *
          Complex.normSq (leftAmp (youngModelOfTwoPaths (P := P) semW p q x.1) sDet) := by
  exact exists_decoheredIntensity_formula_of_holonomyRel
    (P := P) (S := S) (V := V)
    η sem semW obs target_obs α
    (semanticsDerivedUnitPhaseOnHolonomy_of_phaseHypothesis
      (P := P) (S := S) (V := V)
      sem semW obs target_obs phase hPrim)
    x x' hHol sDet

end DerivedPhaseFromWeightedSemantics

-- ============================================================
-- CONCRETE TOY CLOSURE (bridge fully instantiated)
-- ============================================================

section ConcreteToyClosure

abbrev ToyStateInt := _root_.PrimitiveHolonomy.LagState Unit Int
abbrev toyObsUnit : ToyStateInt → Unit := _root_.PrimitiveHolonomy.lagObs (Y := Unit) (B := Int)

def toyTargetObsUnit : ToyPrefix → Unit := fun _ => ()

abbrev ToyFiberBase :=
  _root_.PrimitiveHolonomy.FiberPt (P := ToyPrefix) toyObsUnit toyTargetObsUnit ToyPrefix.base

/-- Unit-modulus complex weight attached to each toy path label. -/
def toyPathUnitWeight : Bool → Complex
  | false => 1
  | true => Complex.I

/-- Relative phase between two toy path labels. -/
def toyRelativePhase : Bool → Bool → Complex
  | false, false => 1
  | false, true => Complex.I
  | true, false => -Complex.I
  | true, true => 1

theorem normSq_toyRelativePhase (p q : Bool) :
    Complex.normSq (toyRelativePhase p q) = 1 := by
  cases p <;> cases q <;> simp [toyRelativePhase]

theorem toyPathUnitWeight_factorization (p q : Bool) :
    toyPathUnitWeight q = toyRelativePhase p q * toyPathUnitWeight p := by
  cases p <;> cases q <;> simp [toyPathUnitWeight, toyRelativePhase]

/-- Complex weighted semantics on the toy history (path-only unit-modulus weights). -/
def toyWeightedSemanticsUnit : WeightedSemantics (P := ToyPrefix) ToyStateInt Complex where
  sem := by
    intro _h _k p
    exact fun _sSrc _sDet => toyPathUnitWeight p

/-- Complete holonomic phase data instantiated on the toy history. -/
def toyCompleteHolonomyPhaseData :
    CompleteHolonomyPhaseData (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
      (sem := toyLagSemantics (Y := Unit))
      (semW := toyWeightedSemanticsUnit)
      toyObsUnit toyTargetObsUnit where
  phase := by
    intro _h _k p q _α _x _x' _hHol _sDet
    exact toyRelativePhase p q
  phase_unit := by
    intro _h _k p q _α _x _x' _hHol _sDet
    exact normSq_toyRelativePhase p q
  phase_coupled := by
    intro _h _k p q _α _x _x' _hHol _sDet
    unfold PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsUnit]
    exact toyPathUnitWeight_factorization p q

/-- The toy complete-data instance induces the existential derived-phase bridge. -/
theorem semanticsDerivedUnitPhaseOnHolonomy_toy :
    ∀ {h k : ToyPrefix} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt
        (P := ToyPrefix) toyObsUnit toyTargetObsUnit h),
      _root_.PrimitiveHolonomy.HolonomyRel
        (P := ToyPrefix) (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit α x x' →
      ∀ sDet : ToyStateInt, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths
          (P := ToyPrefix) toyWeightedSemanticsUnit p q x.1) sDet U := by
  exact semanticsDerivedUnitPhaseOnHolonomy_of_completeHolonomyPhaseData
    (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
    (sem := toyLagSemantics (Y := Unit))
    (semW := toyWeightedSemanticsUnit)
    (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
    toyCompleteHolonomyPhaseData

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
    ∀ x x' : ToyFiberBase,
      _root_.PrimitiveHolonomy.HolonomyRel (P := ToyPrefix)
        (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit alphaFlip x x' →
        ∃ U0 : Complex, Complex.normSq U0 = 1 ∧
          PhaseCoupledAt (fixedPhaseYoungModel A U) () U0 := by
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

/-- Concrete coherent-intensity formula driven by complete holonomic phase data. -/
theorem coherentIntensity_formula_toyHolonomy_from_completeData
    (sDet : ToyStateInt) :
    coherentIntensity (youngModelOfTwoPaths (P := ToyPrefix)
      (h := ToyPrefix.base) (k := ToyPrefix.base)
      toyWeightedSemanticsUnit false true xPlus.1) sDet =
      (2 + 2 * (toyRelativePhase false true).re) *
        Complex.normSq (leftAmp (youngModelOfTwoPaths (P := ToyPrefix)
          (h := ToyPrefix.base) (k := ToyPrefix.base)
          toyWeightedSemanticsUnit false true xPlus.1) sDet) := by
  simpa using
    coherentIntensity_formula_of_holonomyRel_of_completeHolonomyPhaseData
      (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
      (sem := toyLagSemantics (Y := Unit))
      (semW := toyWeightedSemanticsUnit)
      (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
      toyCompleteHolonomyPhaseData
      (α := alphaFlip) (x := xPlus) (x' := xMinus)
      holonomyRel_xPlus_xMinus_alphaFlip sDet

-- ============================================================
-- RICH TOY INSTANCE (phase depends on source and detector states)
-- ============================================================

/-- State-dependent unit phase (constructive/destructive selector). -/
def toyHolonomySign (sSrc sDet : ToyStateInt) : Complex :=
  if sSrc.hidden ≤ sDet.hidden then 1 else -1

theorem normSq_toyHolonomySign (sSrc sDet : ToyStateInt) :
    Complex.normSq (toyHolonomySign sSrc sDet) = 1 := by
  unfold toyHolonomySign
  split_ifs <;> simp

theorem toyHolonomySign_sq_eq_one (sSrc sDet : ToyStateInt) :
    toyHolonomySign sSrc sDet * toyHolonomySign sSrc sDet = 1 := by
  unfold toyHolonomySign
  split_ifs <;> simp

/-- Relative phase for an arbitrary ordered pair of toy paths, now state-dependent. -/
def toyRelativePhaseData (p q : Bool) (sSrc sDet : ToyStateInt) : Complex :=
  match p, q with
  | false, false => 1
  | false, true => toyHolonomySign sSrc sDet
  | true, false => toyHolonomySign sSrc sDet
  | true, true => 1

theorem normSq_toyRelativePhaseData (p q : Bool) (sSrc sDet : ToyStateInt) :
    Complex.normSq (toyRelativePhaseData p q sSrc sDet) = 1 := by
  cases p <;> cases q <;> simp [toyRelativePhaseData, normSq_toyHolonomySign]

/-- Path weights with full micro-state dependence (`sSrc`, `sDet`). -/
def toyWeightedSemanticsHolonomyData : WeightedSemantics (P := ToyPrefix) ToyStateInt Complex where
  sem := by
    intro _h _k p
    exact fun sSrc sDet => if p then toyHolonomySign sSrc sDet else 1

theorem toyWeightedSemanticsHolonomyData_factorization
    (p q : Bool) (sSrc sDet : ToyStateInt) :
    (if q then toyHolonomySign sSrc sDet else 1) =
      toyRelativePhaseData p q sSrc sDet * (if p then toyHolonomySign sSrc sDet else 1) := by
  cases p <;> cases q <;> simp [toyRelativePhaseData, toyHolonomySign_sq_eq_one]

/-- Complete phase data where `phase` really depends on `x.1` and `sDet`. -/
def toyCompleteHolonomyPhaseData_rich :
    CompleteHolonomyPhaseData (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
      (sem := toyLagSemantics (Y := Unit))
      (semW := toyWeightedSemanticsHolonomyData)
      toyObsUnit toyTargetObsUnit where
  phase := by
    intro _h _k p q _α x _x' _hHol sDet
    exact toyRelativePhaseData p q x.1 sDet
  phase_unit := by
    intro _h _k p q _α x _x' _hHol sDet
    exact normSq_toyRelativePhaseData p q x.1 sDet
  phase_coupled := by
    intro _h _k p q _α x _x' _hHol sDet
    unfold PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
    cases p <;> cases q <;> simp [toyWeightedSemanticsHolonomyData, toyRelativePhaseData,
      toyHolonomySign_sq_eq_one]

/-- Derived bridge from the rich complete-data toy instance. -/
theorem semanticsDerivedUnitPhaseOnHolonomy_toy_rich :
    ∀ {h k : ToyPrefix} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt
        (P := ToyPrefix) toyObsUnit toyTargetObsUnit h),
      _root_.PrimitiveHolonomy.HolonomyRel
        (P := ToyPrefix) (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit α x x' →
      ∀ sDet : ToyStateInt, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths
          (P := ToyPrefix) toyWeightedSemanticsHolonomyData p q x.1) sDet U := by
  exact semanticsDerivedUnitPhaseOnHolonomy_of_completeHolonomyPhaseData
    (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
    (sem := toyLagSemantics (Y := Unit))
    (semW := toyWeightedSemanticsHolonomyData)
    (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
    toyCompleteHolonomyPhaseData_rich

/-- Two-path Young model generated by the rich holonomic weighted semantics. -/
abbrev toyYoungFromHolonomyData (sSrc : ToyStateInt) : YoungModel ToyStateInt :=
  youngModelOfTwoPaths (P := ToyPrefix)
    (h := ToyPrefix.base) (k := ToyPrefix.base)
    toyWeightedSemanticsHolonomyData false true sSrc

theorem phaseCoupled_toyYoungFromHolonomyData (sSrc sDet : ToyStateInt) :
    PhaseCoupledAt (toyYoungFromHolonomyData sSrc) sDet (toyHolonomySign sSrc sDet) := by
  unfold toyYoungFromHolonomyData PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
  simp [toyWeightedSemanticsHolonomyData]

/-- Closed coherent-intensity form in the rich toy instance. -/
theorem coherentIntensity_toyYoungFromHolonomyData (sSrc sDet : ToyStateInt) :
    coherentIntensity (toyYoungFromHolonomyData sSrc) sDet =
      2 + 2 * (toyHolonomySign sSrc sDet).re := by
  have hUnit : Complex.normSq (toyHolonomySign sSrc sDet) = 1 :=
    normSq_toyHolonomySign sSrc sDet
  have hMain :
      coherentIntensity (toyYoungFromHolonomyData sSrc) sDet =
        (2 + 2 * (toyHolonomySign sSrc sDet).re) *
          Complex.normSq (leftAmp (toyYoungFromHolonomyData sSrc) sDet) :=
    coherentIntensity_of_phaseCoupled_unit
      (m := toyYoungFromHolonomyData sSrc)
      (x := sDet)
      (U := toyHolonomySign sSrc sDet)
      (phaseCoupled_toyYoungFromHolonomyData sSrc sDet)
      hUnit
  have hLeft :
      Complex.normSq (leftAmp (toyYoungFromHolonomyData sSrc) sDet) = 1 := by
    unfold toyYoungFromHolonomyData leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsHolonomyData]
  rw [hLeft] at hMain
  simpa using hMain

/-- Constructive branch in the rich toy instance. -/
theorem coherentIntensity_toyYoungFromHolonomyData_of_le
    (sSrc sDet : ToyStateInt) (hLe : sSrc.hidden ≤ sDet.hidden) :
    coherentIntensity (toyYoungFromHolonomyData sSrc) sDet = 4 := by
  rw [coherentIntensity_toyYoungFromHolonomyData]
  have hSign : toyHolonomySign sSrc sDet = 1 := by simp [toyHolonomySign, hLe]
  rw [hSign]
  norm_num

/-- Destructive branch in the rich toy instance. -/
theorem coherentIntensity_toyYoungFromHolonomyData_of_gt
    (sSrc sDet : ToyStateInt) (hGt : sDet.hidden < sSrc.hidden) :
    coherentIntensity (toyYoungFromHolonomyData sSrc) sDet = 0 := by
  rw [coherentIntensity_toyYoungFromHolonomyData]
  have hNotLe : ¬ sSrc.hidden ≤ sDet.hidden := not_le.mpr hGt
  have hSign : toyHolonomySign sSrc sDet = -1 := by simp [toyHolonomySign, hNotLe]
  rw [hSign]
  norm_num

/-- Explicit constructive endpoint from source `xPlus` to detector `xPlus`. -/
theorem coherentIntensity_toyHolonomyData_xPlus_to_xPlus :
    coherentIntensity (toyYoungFromHolonomyData xPlus.1) xPlus.1 = 4 := by
  apply coherentIntensity_toyYoungFromHolonomyData_of_le
  simp [xPlus]

/-- Explicit destructive endpoint from source `xPlus` to detector `xMinus`. -/
theorem coherentIntensity_toyHolonomyData_xPlus_to_xMinus :
    coherentIntensity (toyYoungFromHolonomyData xPlus.1) xMinus.1 = 0 := by
  apply coherentIntensity_toyYoungFromHolonomyData_of_gt
  simp [xPlus, xMinus]

-- ============================================================
-- PHASE-FIELD HOLONOMY DATA (constructive, state-dependent)
-- ============================================================

/-- Path-weight semantics from a fully state-dependent complex phase field. -/
def toyWeightedSemanticsPhaseField
    (phase : ToyStateInt → ToyStateInt → Complex) :
    WeightedSemantics (P := ToyPrefix) ToyStateInt Complex where
  sem := by
    intro _h _k p
    exact fun sSrc sDet => if p then phase sSrc sDet else 1

/-- Relative phase for arbitrary `(p,q)` induced by a phase field. -/
def toyRelativePhasePhaseField
    (phase : ToyStateInt → ToyStateInt → Complex)
    (p q : Bool) (sSrc sDet : ToyStateInt) : Complex :=
  let U := phase sSrc sDet
  match p, q with
  | false, false => 1
  | false, true => U
  | true, false => (starRingEnd Complex) U
  | true, true => 1

theorem normSq_toyRelativePhasePhaseField
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1)
    (p q : Bool) (sSrc sDet : ToyStateInt) :
    Complex.normSq (toyRelativePhasePhaseField phase p q sSrc sDet) = 1 := by
  cases p <;> cases q <;> simp [toyRelativePhasePhaseField, hUnit, Complex.normSq_conj]

theorem toyWeightedSemanticsPhaseField_factorization
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1)
    (p q : Bool) (sSrc sDet : ToyStateInt) :
    (if q then phase sSrc sDet else 1) =
      toyRelativePhasePhaseField phase p q sSrc sDet *
        (if p then phase sSrc sDet else 1) := by
  cases p <;> cases q <;> simp [toyRelativePhasePhaseField]
  ·
    have hNormCast : ((Complex.normSq (phase sSrc sDet) : Complex) = 1) := by
      exact_mod_cast hUnit sSrc sDet
    have hConjMul : (starRingEnd Complex) (phase sSrc sDet) * phase sSrc sDet = 1 := by
      calc
        (starRingEnd Complex) (phase sSrc sDet) * phase sSrc sDet
            = (Complex.normSq (phase sSrc sDet) : Complex) := by
                simpa using (Complex.normSq_eq_conj_mul_self (z := phase sSrc sDet)).symm
        _ = 1 := hNormCast
    simpa using hConjMul.symm

/-- Complete holonomic phase data induced by a state-dependent unit phase field. -/
def toyCompleteHolonomyPhaseData_phaseField
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1) :
    CompleteHolonomyPhaseData (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
      (sem := toyLagSemantics (Y := Unit))
      (semW := toyWeightedSemanticsPhaseField phase)
      toyObsUnit toyTargetObsUnit where
  phase := by
    intro _h _k p q _α x _x' _hHol sDet
    exact toyRelativePhasePhaseField phase p q x.1 sDet
  phase_unit := by
    intro _h _k p q _α x _x' _hHol sDet
    exact normSq_toyRelativePhasePhaseField phase hUnit p q x.1 sDet
  phase_coupled := by
    intro _h _k p q _α x _x' _hHol sDet
    unfold PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
    cases p <;> cases q <;> simp [toyWeightedSemanticsPhaseField, toyRelativePhasePhaseField]
    ·
      have hNormCast : ((Complex.normSq (phase x.1 sDet) : Complex) = 1) := by
        exact_mod_cast hUnit x.1 sDet
      have hConjMul : (starRingEnd Complex) (phase x.1 sDet) * phase x.1 sDet = 1 := by
        calc
          (starRingEnd Complex) (phase x.1 sDet) * phase x.1 sDet
              = (Complex.normSq (phase x.1 sDet) : Complex) := by
                  simpa using (Complex.normSq_eq_conj_mul_self (z := phase x.1 sDet)).symm
          _ = 1 := hNormCast
      simpa using hConjMul.symm

/-- Two-path Young model induced by a phase-field holonomic weighted semantics. -/
abbrev toyYoungFromPhaseFieldHolonomyData
    (phase : ToyStateInt → ToyStateInt → Complex)
    (sSrc : ToyStateInt) : YoungModel ToyStateInt :=
  youngModelOfTwoPaths (P := ToyPrefix)
    (h := ToyPrefix.base) (k := ToyPrefix.base)
    (toyWeightedSemanticsPhaseField phase) false true sSrc

/-- Coherent intensity law for phase-field holonomy data. -/
theorem coherentIntensity_toyYoungFromPhaseFieldHolonomyData
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1)
    (sSrc sDet : ToyStateInt) :
    coherentIntensity (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet =
      2 + 2 * (phase sSrc sDet).re := by
  have hPhase :
      PhaseCoupledAt (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet
        (phase sSrc sDet) := by
    unfold toyYoungFromPhaseFieldHolonomyData PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsPhaseField]
  have hMain :
      coherentIntensity (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet =
        (2 + 2 * (phase sSrc sDet).re) *
          Complex.normSq (leftAmp (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet) :=
    coherentIntensity_of_phaseCoupled_unit
      (m := toyYoungFromPhaseFieldHolonomyData phase sSrc)
      (x := sDet)
      (U := phase sSrc sDet)
      hPhase
      (hUnit sSrc sDet)
  have hLeft :
      Complex.normSq (leftAmp (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet) = 1 := by
    unfold toyYoungFromPhaseFieldHolonomyData leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsPhaseField]
  rw [hLeft] at hMain
  simpa using hMain

/-- Decohered intensity law for phase-field holonomy data. -/
theorem decoheredIntensity_toyYoungFromPhaseFieldHolonomyData
    (η : Real)
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1)
    (sSrc sDet : ToyStateInt) :
    decoheredIntensity η (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet =
      2 + 2 * η * (phase sSrc sDet).re := by
  have hPhase :
      PhaseCoupledAt (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet
        (phase sSrc sDet) := by
    unfold toyYoungFromPhaseFieldHolonomyData PhaseCoupledAt rightAmp leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsPhaseField]
  have hMain :
      decoheredIntensity η (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet =
        (2 + 2 * η * (phase sSrc sDet).re) *
          Complex.normSq (leftAmp (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet) :=
    decoheredIntensity_of_phaseCoupled_unit
      (η := η)
      (m := toyYoungFromPhaseFieldHolonomyData phase sSrc)
      (x := sDet)
      (U := phase sSrc sDet)
      hPhase
      (hUnit sSrc sDet)
  have hLeft :
      Complex.normSq (leftAmp (toyYoungFromPhaseFieldHolonomyData phase sSrc) sDet) = 1 := by
    unfold toyYoungFromPhaseFieldHolonomyData leftAmp youngModelOfTwoPaths
    simp [toyWeightedSemanticsPhaseField]
  rw [hLeft] at hMain
  simpa using hMain

/-- Ratio-unitary contract holds for any unit phase field in the toy history. -/
theorem semanticsRatioUnitaryOnHolonomy_toyPhaseField
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1) :
    ∀ {h k : ToyPrefix} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt
        (P := ToyPrefix) toyObsUnit toyTargetObsUnit h),
      _root_.PrimitiveHolonomy.HolonomyRel
        (P := ToyPrefix) (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit α x x' →
      ∀ sDet : ToyStateInt,
        leftAmp (youngModelOfTwoPaths
          (P := ToyPrefix) (toyWeightedSemanticsPhaseField phase) p q x.1) sDet ≠ 0 ∧
        Complex.normSq (rightAmp (youngModelOfTwoPaths
          (P := ToyPrefix) (toyWeightedSemanticsPhaseField phase) p q x.1) sDet) =
          Complex.normSq (leftAmp (youngModelOfTwoPaths
            (P := ToyPrefix) (toyWeightedSemanticsPhaseField phase) p q x.1) sDet) := by
  intro h k p q α x x' _hHol sDet
  constructor
  · cases p with
    | false =>
        simp [leftAmp, youngModelOfTwoPaths, toyWeightedSemanticsPhaseField]
    | true =>
        have hNe : phase x.1 sDet ≠ 0 := by
          intro hz
          have h := hUnit x.1 sDet
          simp [hz] at h
        simpa [leftAmp, youngModelOfTwoPaths, toyWeightedSemanticsPhaseField] using hNe
  · cases p <;> cases q <;> simp [rightAmp, leftAmp, youngModelOfTwoPaths,
      toyWeightedSemanticsPhaseField, hUnit]

/-- Therefore the existential unit-phase bridge is derived from the ratio contract. -/
theorem semanticsDerivedUnitPhaseOnHolonomy_toyPhaseField_of_ratio
    (phase : ToyStateInt → ToyStateInt → Complex)
    (hUnit : ∀ sSrc sDet, Complex.normSq (phase sSrc sDet) = 1) :
    ∀ {h k : ToyPrefix} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
      (x x' : _root_.PrimitiveHolonomy.FiberPt
        (P := ToyPrefix) toyObsUnit toyTargetObsUnit h),
      _root_.PrimitiveHolonomy.HolonomyRel
        (P := ToyPrefix) (toyLagSemantics (Y := Unit)) toyObsUnit toyTargetObsUnit α x x' →
      ∀ sDet : ToyStateInt, ∃ U : Complex,
        Complex.normSq U = 1 ∧
        PhaseCoupledAt (youngModelOfTwoPaths
          (P := ToyPrefix) (toyWeightedSemanticsPhaseField phase) p q x.1) sDet U := by
  exact semanticsDerivedUnitPhaseOnHolonomy_of_ratioUnitary
    (P := ToyPrefix) (S := ToyStateInt) (V := Unit)
    (sem := toyLagSemantics (Y := Unit))
    (semW := toyWeightedSemanticsPhaseField phase)
    (obs := toyObsUnit) (target_obs := toyTargetObsUnit)
    (semanticsRatioUnitaryOnHolonomy_toyPhaseField phase hUnit)

-- ============================================================
-- ANGLE PARAMETRIZATION (explicit fringe formulas)
-- ============================================================

/-- The angle phase `⟨cos θ, sin θ⟩` always has modulus 1. -/
theorem normSq_phase_of_angle (θ : Real) :
    Complex.normSq (⟨Real.cos θ, Real.sin θ⟩ : Complex) = 1 := by
  simpa [Complex.normSq, pow_two] using Real.cos_sq_add_sin_sq θ

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

/-- Opposite phase: incoherent-to-coherent jump is exactly `2|A_L|^2`. -/
theorem incoherentIntensity_sub_coherentIntensity_of_oppositePhase {X : Type u}
    (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    incoherentIntensity m x - coherentIntensity m x =
      (2 : Real) * Complex.normSq (leftAmp m x) := by
  rw [incoherentIntensity_of_oppositePhase m x hOpp,
    coherentIntensity_zero_of_oppositePhase m x hOpp]
  ring

/-- Opposite phase: decoherence gap to incoherent level is exactly `2η|A_L|^2`. -/
theorem incoherentIntensity_sub_decoheredIntensity_of_oppositePhase {X : Type u}
    (η : Real) (m : YoungModel X) (x : X)
    (hOpp : rightAmp m x = - leftAmp m x) :
    incoherentIntensity m x - decoheredIntensity η m x =
      (2 * η) * Complex.normSq (leftAmp m x) := by
  rw [incoherentIntensity_of_oppositePhase m x hOpp,
    decoheredIntensity_of_oppositePhase η m x hOpp]
  ring

end Regimes

-- ============================================================
-- CHSH PHASE-ONLY LAYER (holonomy-friendly formulation)
-- ============================================================

section CHSHPhaseOnly

/-- Phase-only correlation attached to a local pair of unit phases. -/
def phaseCorrelation (u v : Complex) : Real :=
  - (u * (starRingEnd Complex) v).re

/-- CHSH expression in terms of four local phase choices `(u0,u1,v0,v1)`. -/
def chshPhase (u0 u1 v0 v1 : Complex) : Real :=
  phaseCorrelation u0 v0 + phaseCorrelation u0 v1 +
    phaseCorrelation u1 v0 - phaseCorrelation u1 v1

/-- Factorized CHSH form: one `(+ )` branch and one `(- )` branch on Bob's side. -/
theorem chshPhase_eq_neg_re_factorized (u0 u1 v0 v1 : Complex) :
    chshPhase u0 u1 v0 v1 =
      - (u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re := by
  unfold chshPhase phaseCorrelation
  simp [sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm]

/-- Complex parallelogram identity specialized to unit-modulus `v0,v1`. -/
theorem normSq_add_plus_normSq_sub_eq_four_of_unit (v0 v1 : Complex)
    (hV0 : Complex.normSq v0 = 1)
    (hV1 : Complex.normSq v1 = 1) :
    Complex.normSq (v0 + v1) + Complex.normSq (v0 - v1) = 4 := by
  calc
    Complex.normSq (v0 + v1) + Complex.normSq (v0 - v1)
        = (Complex.normSq v0 + Complex.normSq v1 + 2 * (v0 * (starRingEnd Complex) v1).re) +
          (Complex.normSq v0 + Complex.normSq v1 - 2 * (v0 * (starRingEnd Complex) v1).re) := by
            simp [Complex.normSq_add, Complex.normSq_sub]
    _ = 2 * (Complex.normSq v0 + Complex.normSq v1) := by ring
    _ = 4 := by nlinarith [hV0, hV1]

/-- Tsirelson bound in phase-only form under unit-modulus local phases. -/
theorem abs_chshPhase_le_two_sqrt_two_of_unit
    (u0 u1 v0 v1 : Complex)
    (hU0 : Complex.normSq u0 = 1)
    (hU1 : Complex.normSq u1 = 1)
    (hV0 : Complex.normSq v0 = 1)
    (hV1 : Complex.normSq v1 = 1) :
    |chshPhase u0 u1 v0 v1| ≤ 2 * Real.sqrt 2 := by
  rw [chshPhase_eq_neg_re_factorized]
  have hAbsNeg :
      |-(u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re| =
        |(u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re| := by
    simpa using
      abs_neg
        ((u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re)
  rw [hAbsNeg]
  have hStep1 :
      |(u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re| ≤
        ‖u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)‖ := by
    simpa using
      (RCLike.abs_re_le_norm
        (u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)))
  have hStep2 :
      ‖u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)‖ ≤
        ‖u0 * (starRingEnd Complex) (v0 + v1)‖ +
          ‖u1 * (starRingEnd Complex) (v0 - v1)‖ := by
    simpa using
      norm_add_le (u0 * (starRingEnd Complex) (v0 + v1))
        (u1 * (starRingEnd Complex) (v0 - v1))
  have hU0norm : ‖u0‖ = 1 := by
    have hSq : ‖u0‖ ^ 2 = 1 := by simpa [Complex.normSq_eq_norm_sq] using hU0
    have hNonneg : 0 ≤ ‖u0‖ := norm_nonneg u0
    nlinarith
  have hU1norm : ‖u1‖ = 1 := by
    have hSq : ‖u1‖ ^ 2 = 1 := by simpa [Complex.normSq_eq_norm_sq] using hU1
    have hNonneg : 0 ≤ ‖u1‖ := norm_nonneg u1
    nlinarith
  have hConjAddExpanded :
      ‖(starRingEnd Complex) v0 + (starRingEnd Complex) v1‖ = ‖v0 + v1‖ := by
    calc
      ‖(starRingEnd Complex) v0 + (starRingEnd Complex) v1‖
          = ‖(starRingEnd Complex) (v0 + v1)‖ := by simp
      _ = ‖v0 + v1‖ := by simpa using (Complex.norm_conj (v0 + v1))
  have hConjSubExpanded :
      ‖(starRingEnd Complex) v0 - (starRingEnd Complex) v1‖ = ‖v0 - v1‖ := by
    calc
      ‖(starRingEnd Complex) v0 - (starRingEnd Complex) v1‖
          = ‖(starRingEnd Complex) (v0 - v1)‖ := by simp
      _ = ‖v0 - v1‖ := by simpa using (Complex.norm_conj (v0 - v1))
  have hStep3 :
      ‖u0 * (starRingEnd Complex) (v0 + v1)‖ +
          ‖u1 * (starRingEnd Complex) (v0 - v1)‖ =
        ‖v0 + v1‖ + ‖v0 - v1‖ := by
    calc
      ‖u0 * (starRingEnd Complex) (v0 + v1)‖ +
          ‖u1 * (starRingEnd Complex) (v0 - v1)‖
          = ‖u0‖ * ‖(starRingEnd Complex) (v0 + v1)‖ +
              ‖u1‖ * ‖(starRingEnd Complex) (v0 - v1)‖ := by
                simp
      _ = ‖u0‖ * ‖v0 + v1‖ + ‖u1‖ * ‖v0 - v1‖ := by
            simp [hConjAddExpanded, hConjSubExpanded]
      _ = ‖v0 + v1‖ + ‖v0 - v1‖ := by simp [hU0norm, hU1norm]
  have hPar :
      ‖v0 + v1‖ ^ 2 + ‖v0 - v1‖ ^ 2 = 4 := by
    simpa [Complex.normSq_eq_norm_sq] using
      (normSq_add_plus_normSq_sub_eq_four_of_unit v0 v1 hV0 hV1)
  let a : Real := ‖v0 + v1‖
  let b : Real := ‖v0 - v1‖
  have hAB : a ^ 2 + b ^ 2 = 4 := by simpa [a, b] using hPar
  have hSumSq : (a + b) ^ 2 ≤ 8 := by
    have hDiffSqNonneg : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    nlinarith [hAB, hDiffSqNonneg]
  have hSumLeSqrt8 : a + b ≤ Real.sqrt 8 := by
    have hNonneg : 0 ≤ a + b := by
      have ha : 0 ≤ a := by simp [a]
      have hb : 0 ≤ b := by simp [b]
      nlinarith
    exact (Real.le_sqrt hNonneg (by norm_num)).2 hSumSq
  have hSqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 8 = Real.sqrt (4 * 2) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 2 := by
            rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
      _ = 2 * Real.sqrt 2 := by norm_num
  have hStep4 :
      ‖u0 * (starRingEnd Complex) (v0 + v1)‖ +
          ‖u1 * (starRingEnd Complex) (v0 - v1)‖ ≤
        2 * Real.sqrt 2 := by
    rw [hStep3]
    simpa [a, b, hSqrt8] using hSumLeSqrt8
  have hMain :
      |(u0 * (starRingEnd Complex) (v0 + v1) +
          u1 * (starRingEnd Complex) (v0 - v1)).re| ≤
        2 * Real.sqrt 2 := by
    exact le_trans hStep1 (le_trans hStep2 hStep4)
  simpa using hMain

/-- Explicit phase witness saturating Tsirelson: `|CHSH| = 2 * sqrt 2`. -/
theorem exists_phase_witness_abs_chsh_eq_two_sqrt_two :
    ∃ u0 u1 v0 v1 : Complex,
      Complex.normSq u0 = 1 ∧
      Complex.normSq u1 = 1 ∧
      Complex.normSq v0 = 1 ∧
      Complex.normSq v1 = 1 ∧
      |chshPhase u0 u1 v0 v1| = 2 * Real.sqrt 2 := by
  let u0 : Complex := 1
  let u1 : Complex := Complex.I
  let s : Real := Real.sqrt 2 / 2
  let v0 : Complex := ⟨s, s⟩
  let v1 : Complex := ⟨s, -s⟩
  refine ⟨u0, u1, v0, v1, ?_⟩
  have hsq : s ^ 2 = (1 : Real) / 2 := by
    dsimp [s]
    have hsqrt2sq : (Real.sqrt 2) ^ 2 = (2 : Real) := by
      exact Real.sq_sqrt (by norm_num)
    nlinarith [hsqrt2sq]
  have hU0 : Complex.normSq u0 = 1 := by simp [u0]
  have hU1 : Complex.normSq u1 = 1 := by simp [u1]
  have hV0 : Complex.normSq v0 = 1 := by
    dsimp [v0]
    nlinarith [hsq]
  have hV1 : Complex.normSq v1 = 1 := by
    dsimp [v1]
    nlinarith [hsq]
  have hAdd : v0 + v1 = (⟨Real.sqrt 2, 0⟩ : Complex) := by
    apply Complex.ext <;> dsimp [v0, v1, s] <;> ring
  have hSub : v0 - v1 = (⟨0, Real.sqrt 2⟩ : Complex) := by
    apply Complex.ext <;> dsimp [v0, v1, s] <;> ring
  have hChsh : chshPhase u0 u1 v0 v1 = -(2 * Real.sqrt 2) := by
    rw [chshPhase_eq_neg_re_factorized, hAdd, hSub]
    dsimp [u0, u1]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  refine ⟨hU0, hU1, hV0, hV1, ?_⟩
  rw [hChsh]
  rw [abs_neg]
  have hNonneg : 0 ≤ 2 * Real.sqrt 2 := by
    have hSqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  rw [abs_of_nonneg hNonneg]

/-- Therefore the phase-only CHSH layer strictly violates the classical deterministic bound `2`. -/
theorem exists_phase_witness_abs_chsh_gt_two :
    ∃ u0 u1 v0 v1 : Complex,
      Complex.normSq u0 = 1 ∧
      Complex.normSq u1 = 1 ∧
      Complex.normSq v0 = 1 ∧
      Complex.normSq v1 = 1 ∧
      2 < |chshPhase u0 u1 v0 v1| := by
  rcases exists_phase_witness_abs_chsh_eq_two_sqrt_two with
      ⟨u0, u1, v0, v1, hU0, hU1, hV0, hV1, hEq⟩
  refine ⟨u0, u1, v0, v1, hU0, hU1, hV0, hV1, ?_⟩
  rw [hEq]
  have hSqrt2 : (1 : Real) < Real.sqrt 2 := by
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  nlinarith

/-- Classical deterministic CHSH expression on real local outcomes. -/
def chshDeterministic (a0 a1 b0 b1 : Real) : Real :=
  a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

/-- Real value with square `1` has absolute value `1`. -/
theorem abs_eq_one_of_sq_eq_one_real {x : Real} (hx : x ^ 2 = 1) : |x| = 1 := by
  have hsq : |x| ^ 2 = 1 := by simpa [sq_abs] using hx
  have hnonneg : 0 ≤ |x| := abs_nonneg x
  nlinarith

/-- Classical CHSH bound under deterministic local outcomes (`aᵢ,bⱼ ∈ {±1}`). -/
theorem abs_chshDeterministic_le_two_of_sq_eq_one
    (a0 a1 b0 b1 : Real)
    (hA0 : a0 ^ 2 = 1) (hA1 : a1 ^ 2 = 1)
    (hB0 : b0 ^ 2 = 1) (hB1 : b1 ^ 2 = 1) :
    |chshDeterministic a0 a1 b0 b1| ≤ 2 := by
  have hA0abs : |a0| = 1 := abs_eq_one_of_sq_eq_one_real hA0
  have hA1abs : |a1| = 1 := abs_eq_one_of_sq_eq_one_real hA1
  have hBpar : (b0 + b1) * (b0 - b1) = 0 := by
    nlinarith [hB0, hB1]
  have hBprodAbs : |b0 + b1| * |b0 - b1| = 0 := by
    have hAbs : |(b0 + b1) * (b0 - b1)| = 0 := by
      simp [hBpar]
    simpa [abs_mul] using hAbs
  have hBsumSq : |b0 + b1| ^ 2 + |b0 - b1| ^ 2 = 4 := by
    calc
      |b0 + b1| ^ 2 + |b0 - b1| ^ 2
          = (b0 + b1) ^ 2 + (b0 - b1) ^ 2 := by simp [sq_abs]
      _ = 4 := by nlinarith [hB0, hB1]
  let x : Real := |b0 + b1|
  let y : Real := |b0 - b1|
  have hx : 0 ≤ x := by simp [x]
  have hy : 0 ≤ y := by simp [y]
  have hxy : x * y = 0 := by simpa [x, y] using hBprodAbs
  have hxySq : x ^ 2 + y ^ 2 = 4 := by simpa [x, y] using hBsumSq
  have hxySumSq : (x + y) ^ 2 = 4 := by
    nlinarith [hxy, hxySq]
  have hxySum : x + y = 2 := by
    nlinarith [hx, hy, hxySumSq]
  have hFac : chshDeterministic a0 a1 b0 b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by
    unfold chshDeterministic
    ring_nf
  have hTri :
      |a0 * (b0 + b1) + a1 * (b0 - b1)| ≤
        |a0 * (b0 + b1)| + |a1 * (b0 - b1)| := by
    simpa [Real.norm_eq_abs] using
      (norm_add_le (a0 * (b0 + b1)) (a1 * (b0 - b1)))
  rw [hFac]
  calc
    |a0 * (b0 + b1) + a1 * (b0 - b1)|
        ≤ |a0 * (b0 + b1)| + |a1 * (b0 - b1)| := hTri
    _ = |a0| * |b0 + b1| + |a1| * |b0 - b1| := by
          simp [abs_mul]
    _ = x + y := by simp [x, y, hA0abs, hA1abs]
    _ = 2 := hxySum

end CHSHPhaseOnly

end PrimitiveHolonomy.Physics
