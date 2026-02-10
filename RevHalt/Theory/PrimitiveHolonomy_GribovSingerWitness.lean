import RevHalt.Theory.PrimitiveHolonomy_instance

/-!
# Primitive Holonomy: Concrete Gribov-Singer Witness

This file isolates a concrete, non-vacuous gauge-fixing obstruction witness
in the toy `PrimitiveHolonomy_instance` model.

It does not add new axioms; it repackages existing instance-level facts into a
compact "what fails globally under admissible gauges" module.
-/

namespace PrimitiveHolonomy

section GribovSingerWitness

/-- Admissible gauges in this witness module: reflexive gauges only. -/
abbrev ToyOK : Gauge (P := Unit) toyObs toyTargetObs → Prop :=
  GaugeRefl (P := Unit) toyObs toyTargetObs

/-- Single problematic 2-cell used in the instance witness. -/
abbrev ToyJ : Set (Cell (P := Unit)) :=
  ({cell₁} : Set (Cell (P := Unit)))

/-- The admissibility predicate is non-vacuous (identity gauge is admissible). -/
theorem toy_exists_admissible_gauge : ∃ φ : Gauge (P := Unit) toyObs toyTargetObs, ToyOK φ := by
  exact ⟨idGauge, idGauge_refl⟩

/-- Concrete obstruction witness in the toy model under admissible gauges. -/
theorem toy_obstructionWrt : ObstructionWrt (P := Unit) toySemantics toyObs toyTargetObs ToyOK ToyJ := by
  simpa [ToyOK, ToyJ] using obstructionWrt_refl_singleton

/-- Global gauge fixing fails under the same admissibility condition. -/
theorem toy_not_autoRegulatedWrt :
    ¬ AutoRegulatedWrt (P := Unit) toySemantics toyObs toyTargetObs ToyOK ToyJ := by
  simpa [ToyOK, ToyJ] using not_autoRegulatedWrt_refl_singleton

/-- Equivalent twisted-on-cell form: every admissible gauge exhibits a twisted witness. -/
theorem toy_every_admissible_has_twisted_cell :
    ∀ φ : Gauge (P := Unit) toyObs toyTargetObs, ToyOK φ →
      ∃ c, c ∈ ToyJ ∧ TwistedOnCell (P := Unit) toySemantics toyObs toyTargetObs φ c := by
  exact
    (obstructionWrt_iff_twistedOnCell
      (P := Unit) toySemantics toyObs toyTargetObs ToyOK ToyJ).1 toy_obstructionWrt

/-- In particular, every admissible gauge is bad on `cell₁` itself. -/
theorem toy_no_goodGaugeForCell1_of_admissible
    (φ : Gauge (P := Unit) toyObs toyTargetObs) (hOK : ToyOK φ) :
    ¬ GoodGaugeForCellWrt (P := Unit) toySemantics toyObs toyTargetObs ToyOK cell₁ φ := by
  have hTwAll := toy_every_admissible_has_twisted_cell φ hOK
  rcases hTwAll with ⟨c, hcJ, hTw⟩
  have hc : c = cell₁ := by
    simpa [ToyJ] using hcJ
  subst hc
  exact
    twistedOnCell_not_goodGaugeForCellWrt
      (P := Unit) toySemantics toyObs toyTargetObs ToyOK hTw

end GribovSingerWitness

end PrimitiveHolonomy

