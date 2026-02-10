import RevHalt.Theory.PrimitiveHolonomy_GribovSingerWitness

/-!
# Primitive Holonomy: Orbit Gauge Witness (Stable Re-export)

This module provides a compact, compilable witness layer in a dedicated file.
It re-exports the concrete toy obstruction package already proved in
`PrimitiveHolonomy_GribovSingerWitness`.
-/

namespace PrimitiveHolonomy

section OrbitGaugeWitness

abbrev OrbitOK : Gauge (P := Unit) toyObs toyTargetObs → Prop :=
  ToyOK

abbrev OrbitJ : Set (Cell (P := Unit)) :=
  ToyJ

theorem orbit_exists_admissible_gauge :
    ∃ φ : Gauge (P := Unit) toyObs toyTargetObs, OrbitOK φ := by
  simpa [OrbitOK] using toy_exists_admissible_gauge

theorem orbit_obstructionWrt :
    ObstructionWrt (P := Unit) toySemantics toyObs toyTargetObs OrbitOK OrbitJ := by
  simpa [OrbitOK, OrbitJ] using toy_obstructionWrt

theorem orbit_not_autoRegulatedWrt :
    ¬ AutoRegulatedWrt (P := Unit) toySemantics toyObs toyTargetObs OrbitOK OrbitJ := by
  simpa [OrbitOK, OrbitJ] using toy_not_autoRegulatedWrt

theorem orbit_every_admissible_has_twisted_cell :
    ∀ φ : Gauge (P := Unit) toyObs toyTargetObs, OrbitOK φ →
      ∃ c, c ∈ OrbitJ ∧ TwistedOnCell (P := Unit) toySemantics toyObs toyTargetObs φ c := by
  simpa [OrbitOK, OrbitJ] using toy_every_admissible_has_twisted_cell

end OrbitGaugeWitness

end PrimitiveHolonomy

