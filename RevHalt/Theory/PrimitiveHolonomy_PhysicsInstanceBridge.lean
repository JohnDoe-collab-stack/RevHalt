import RevHalt.Theory.PrimitiveHolonomy_Physics
import RevHalt.Theory.PrimitiveHolonomy_instance
import RevHalt.Theory.PrimitiveHolonomy_GribovSingerWitness

/-!
# Primitive Holonomy: Physics Instance Bridge

Concrete bridge lemmas from `PrimitiveHolonomy_instance` to the physics
asymmetry vocabulary, with hypotheses discharged on the toy `Unit` model.
-/

namespace PrimitiveHolonomy.Physics

/-- The toy state space is equivalent to `Bool` via the hidden bit. -/
def toyStateEquivBool : _root_.PrimitiveHolonomy.ToyState ≃ Bool where
  toFun := fun s => s.hidden
  invFun := fun b => ⟨(), b⟩
  left_inv := by
    intro s
    cases s with
    | mk vis hid =>
      cases vis
      rfl
  right_inv := by
    intro b
    rfl

/-- Decidable equality on toy states (constructive, via hidden Bool). -/
instance toyStateDecidableEq : DecidableEq _root_.PrimitiveHolonomy.ToyState := by
  intro a b
  cases a with
  | mk va ha =>
    cases b with
    | mk vb hb =>
      cases va
      cases vb
      refine decidable_of_iff (ha = hb) ?_
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl

/-- Finite toy state space (equivalent to `Bool`). -/
instance toyStateFintype : Fintype _root_.PrimitiveHolonomy.ToyState :=
  Fintype.ofEquiv Bool toyStateEquivBool.symm

/-- Physics structure on the toy state space (`LagState Unit Bool`):
`C` flips the hidden bit, and `(B,L,N_CS)` are the signed hidden value. -/
def toyStateBoolPhysics : ParticlePhysics _root_.PrimitiveHolonomy.ToyState where
  C := fun s => ⟨s.visible, !s.hidden⟩
  C_invol := by
    intro s
    cases s
    simp
  B := fun s => if s.hidden then 1 else -1
  B_odd := by
    intro s
    cases s with
    | mk vis hid =>
      cases hid <;> simp
  L := fun s => if s.hidden then 1 else -1
  L_odd := by
    intro s
    cases s with
    | mk vis hid =>
      cases hid <;> simp
  N_CS := fun s => if s.hidden then 1 else -1

/-- Non-fixed `C`-pairs automatically have nonzero baryon charge
in the toy Bool-hidden physics. -/
theorem b_nonfixed_of_toyStateBoolPhysics
    (s : _root_.PrimitiveHolonomy.ToyState) :
    (toyStateBoolPhysics.C s) ≠ s →
    (toyStateBoolPhysics.B s) ≠ 0 := by
  intro _hC
  cases s with
  | mk vis hid =>
    cases hid <;> simp [toyStateBoolPhysics]

/-- The lag-conjugacy hypothesis is derivable in the toy instance. -/
theorem lagConjugacyHypothesis_toyStateBool :
    LagConjugacyHypothesis
      (P := Unit)
      (S := _root_.PrimitiveHolonomy.ToyState)
      (V := Unit)
      toyStateBoolPhysics
      _root_.PrimitiveHolonomy.toySemantics
      _root_.PrimitiveHolonomy.toyObs
      _root_.PrimitiveHolonomy.toyTargetObs
      _root_.PrimitiveHolonomy.α₁
      _root_.PrimitiveHolonomy.ToyPath.step := by
  intro x x' hxne hHol _hx _hx'
  rcases hHol with ⟨y, hp, hq⟩
  have hxFalse : x.1.hidden = false := hp.1
  have hyTrue : y.1.hidden = true := hp.2.1
  have hx'Eqy : x'.1 = y.1 := by
    simpa [_root_.PrimitiveHolonomy.R_q, _root_.PrimitiveHolonomy.relId] using hq
  have hx'True : x'.1.hidden = true := by
    simpa [hx'Eqy] using hyTrue
  have hEqConj : x'.1 = toyStateBoolPhysics.C x.1 := by
    cases xs : x.1 with
    | mk vis hid =>
      cases xs' : x'.1 with
      | mk vis' hid' =>
        have hhid : hid = false := by simpa [xs] using hxFalse
        have hhid' : hid' = true := by simpa [xs'] using hx'True
        subst hhid
        subst hhid'
        simp [toyStateBoolPhysics]
  refine ⟨hEqConj, ?_⟩
  intro hFix
  apply hxne
  apply Subtype.ext
  exact (hEqConj.trans hFix).symm

/-- Fully discharged toy-instance asymmetry theorem:
the existing lag witness yields a distribution with nonzero expected baryon number. -/
theorem lagEvent_implies_exists_distribution_with_expectedB_ne_zero_toyStateBoolPhysics
    :
    ∃ μ : _root_.PrimitiveHolonomy.ToyState → Rat,
      ExpectedB toyStateBoolPhysics μ ≠ 0 := by
  exact lagEvent_implies_exists_distribution_with_expectedB_ne_zero
    (P := Unit)
    (S := _root_.PrimitiveHolonomy.ToyState)
    (V := Unit)
    (phys := toyStateBoolPhysics)
    _root_.PrimitiveHolonomy.toySemantics
    _root_.PrimitiveHolonomy.toyObs
    _root_.PrimitiveHolonomy.toyTargetObs
    _root_.PrimitiveHolonomy.α₁
    _root_.PrimitiveHolonomy.ToyPath.step
    lagConjugacyHypothesis_toyStateBool
    _root_.PrimitiveHolonomy.lag_event_witness
    (by
      intro s hs
      exact b_nonfixed_of_toyStateBoolPhysics s hs)

/-- In the toy Bool-hidden physics, ABJ holds globally for one family (`N_f = 1`). -/
theorem abjOnSphaleronPairs_toyStateBoolPhysics_nf_one :
    ABJOnSphaleronPairs toyStateBoolPhysics 1 := by
  intro s1 s2 _hSph
  unfold SatisfiesABJ DeltaBL DeltaNCS
  simp [toyStateBoolPhysics]
  ring

/-- `N_CS` is injective on toy states for `toyStateBoolPhysics`. -/
theorem toyStateBoolPhysics_ncs_injective :
    Function.Injective toyStateBoolPhysics.N_CS := by
  intro s t h
  cases s with
  | mk vis hid =>
    cases vis
    cases t with
    | mk vis' hid' =>
      cases vis'
      cases hid <;> cases hid' <;> simp [toyStateBoolPhysics] at h ⊢

/-- Concrete no-contract version:
toy obstruction already forces a non-zero `DeltaBL` witness for each admissible gauge. -/
theorem toy_obstruction_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := Unit)
      _root_.PrimitiveHolonomy.toyObs _root_.PrimitiveHolonomy.toyTargetObs,
      _root_.PrimitiveHolonomy.ToyOK φ →
        ∃ s1 s2 : _root_.PrimitiveHolonomy.ToyState,
          DeltaBL toyStateBoolPhysics s1 s2 ≠ 0 := by
  exact
    obstructionWrt_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge_of_ncsJump_and_abj
      (P := Unit) (S := _root_.PrimitiveHolonomy.ToyState) (V := Unit)
      (phys := toyStateBoolPhysics) (N_f := 1)
      _root_.PrimitiveHolonomy.toySemantics
      _root_.PrimitiveHolonomy.toyObs
      _root_.PrimitiveHolonomy.toyTargetObs
      _root_.PrimitiveHolonomy.ToyOK
      _root_.PrimitiveHolonomy.ToyJ
      (by norm_num)
      (ncsJumpOnTwistedWitness_of_ncs_injective
        (P := Unit) (S := _root_.PrimitiveHolonomy.ToyState) (V := Unit)
        toyStateBoolPhysics
        _root_.PrimitiveHolonomy.toySemantics
        _root_.PrimitiveHolonomy.toyObs
        _root_.PrimitiveHolonomy.toyTargetObs
        toyStateBoolPhysics_ncs_injective)
      abjOnSphaleronPairs_toyStateBoolPhysics_nf_one
      _root_.PrimitiveHolonomy.toy_obstructionWrt

end PrimitiveHolonomy.Physics
