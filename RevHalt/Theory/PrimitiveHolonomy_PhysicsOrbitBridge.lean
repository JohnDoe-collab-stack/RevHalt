import RevHalt.Theory.PrimitiveHolonomy_Physics
import RevHalt.Theory.PrimitiveHolonomy_OrbitGaugeWitness

/-!
# Primitive Holonomy: Physics Orbit-Bridge

Concrete bridge lemmas from the orbit witness module to the
`PrimitiveHolonomy.Physics.GaugeFixingBridge` vocabulary.
-/

namespace PrimitiveHolonomy.Physics

/-- The concrete orbit witness is an obstruction in the physics bridge vocabulary. -/
theorem orbitGaugeFixingObstructed :
    GaugeFixingObstructed (P := Unit)
      _root_.PrimitiveHolonomy.toySemantics
      _root_.PrimitiveHolonomy.toyObs
      _root_.PrimitiveHolonomy.toyTargetObs
      _root_.PrimitiveHolonomy.OrbitOK
      _root_.PrimitiveHolonomy.OrbitJ := by
  simpa [GaugeFixingObstructed] using
    (_root_.PrimitiveHolonomy.orbit_obstructionWrt)

/-- Hence the concrete orbit witness is not globally gauge-fixable. -/
theorem orbit_not_globalGaugeFixable :
    ¬ GlobalGaugeFixable (P := Unit)
      _root_.PrimitiveHolonomy.toySemantics
      _root_.PrimitiveHolonomy.toyObs
      _root_.PrimitiveHolonomy.toyTargetObs
      _root_.PrimitiveHolonomy.OrbitOK
      _root_.PrimitiveHolonomy.OrbitJ := by
  exact obstructed_implies_not_globalGaugeFixable
    (P := Unit)
    _root_.PrimitiveHolonomy.toySemantics
    _root_.PrimitiveHolonomy.toyObs
    _root_.PrimitiveHolonomy.toyTargetObs
    _root_.PrimitiveHolonomy.OrbitOK
    _root_.PrimitiveHolonomy.OrbitJ
    orbitGaugeFixingObstructed

/-- Twisted witness form for every admissible gauge, phrased with physics bridge lemmas. -/
theorem orbit_every_admissible_has_twisted_cell_physics :
    ∀ φ : _root_.PrimitiveHolonomy.Gauge (P := Unit)
      _root_.PrimitiveHolonomy.toyObs _root_.PrimitiveHolonomy.toyTargetObs,
      _root_.PrimitiveHolonomy.OrbitOK φ →
        ∃ c, c ∈ _root_.PrimitiveHolonomy.OrbitJ ∧
          _root_.PrimitiveHolonomy.TwistedOnCell (P := Unit)
            _root_.PrimitiveHolonomy.toySemantics
            _root_.PrimitiveHolonomy.toyObs
            _root_.PrimitiveHolonomy.toyTargetObs φ c := by
  exact
    (obstruction_iff_twisted_witness_per_admissible_gauge
      (P := Unit)
      _root_.PrimitiveHolonomy.toySemantics
      _root_.PrimitiveHolonomy.toyObs
      _root_.PrimitiveHolonomy.toyTargetObs
      _root_.PrimitiveHolonomy.OrbitOK
      _root_.PrimitiveHolonomy.OrbitJ).1
      orbitGaugeFixingObstructed

end PrimitiveHolonomy.Physics

