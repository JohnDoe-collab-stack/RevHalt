import RevHalt.Theory.Stabilization
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order.ScottTopology

/-!
# RevHalt.Theory.ScottTopology

This file makes explicit the standard domain-theoretic/topological reading of the core
trace predicates:

- `Halts` is **Scott-open** (Σ₁ / finitely observable).
- `Stabilizes` is **Scott-closed** (Π₁ / limit property).

We use the Scott topology on the preorder `Trace := ℕ → Prop` (pointwise implication order),
as provided by `Mathlib.Topology.Order.ScottTopology` via the type synonym `Topology.WithScott`.
-/

namespace RevHalt

open Topology

instance : CompleteLattice Trace := by
  delta Trace
  infer_instance

/-- The set of halting traces. -/
def HaltsSet : Set Trace := {T | Halts T}

/-- The set of stabilizing traces. -/
def StabilizesSet : Set Trace := {T | Stabilizes T}

theorem haltsSet_isUpper : IsUpperSet (HaltsSet) := by
  intro T U hTU hT
  rcases hT with ⟨n, hn⟩
  exact ⟨n, hTU n hn⟩

theorem stabilizesSet_isLower : IsLowerSet (StabilizesSet) := by
  intro T U hUT hT n hn
  exact hT n (hUT n hn)

theorem haltsSet_dirSupInacc : DirSupInacc (HaltsSet) := by
  refine (dirSupInacc_iff_forall_sSup (α := Trace) (s := HaltsSet)).2 ?_
  intro d _hd hdir hSupHalts
  rcases hSupHalts with ⟨n, hn⟩
  have hex : ∃ T : Trace, T ∈ d ∧ T n := (unary_relation_sSup_iff (s := d) (a := n)).1 hn
  rcases hex with ⟨T, hTd, hTn⟩
  refine ⟨T, ?_⟩
  exact ⟨hTd, ⟨n, hTn⟩⟩

theorem haltsSet_isOpen_scott : @IsOpen (Topology.WithScott Trace) _ (HaltsSet) := by
  refine
    (Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn
          (α := Topology.WithScott Trace) (D := Set.univ) (s := HaltsSet)).2 ?_
  refine ⟨haltsSet_isUpper, (haltsSet_dirSupInacc).dirSupInaccOn⟩

theorem stabilizesSet_eq_compl_haltsSet : StabilizesSet = (HaltsSet)ᶜ := by
  ext T
  simp [StabilizesSet, HaltsSet, Stabilizes_iff_NotHalts]

theorem stabilizesSet_isClosed_scott : @IsClosed (Topology.WithScott Trace) _ (StabilizesSet) := by
  have h : @IsClosed (Topology.WithScott Trace) _ ((HaltsSet)ᶜ) :=
    (haltsSet_isOpen_scott).isClosed_compl
  simpa [stabilizesSet_eq_compl_haltsSet] using h

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.haltsSet_isUpper
#print axioms RevHalt.stabilizesSet_isLower
#print axioms RevHalt.haltsSet_dirSupInacc
#print axioms RevHalt.haltsSet_isOpen_scott
#print axioms RevHalt.stabilizesSet_eq_compl_haltsSet
#print axioms RevHalt.stabilizesSet_isClosed_scott
