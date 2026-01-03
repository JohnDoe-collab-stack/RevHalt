import RevHalt.Theory.Stabilization
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
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

theorem stabilizesSet_not_isOpen_scott :
    ¬ @IsOpen (Topology.WithScott Trace) _ (StabilizesSet) := by
  intro hOpen
  have hUpper : IsUpperSet StabilizesSet :=
    Topology.IsScott.isUpperSet_of_isOpen (α := Topology.WithScott Trace) (D := Set.univ) (s := StabilizesSet)
      hOpen
  have hbot : (⊥ : Trace) ∈ StabilizesSet := by
    intro n hn
    cases hn
  have htop : (⊤ : Trace) ∈ StabilizesSet := by
    have hle : (⊥ : Trace) ≤ (⊤ : Trace) := bot_le
    exact hUpper hle hbot
  have : ¬ Stabilizes (⊤ : Trace) := by
    intro h
    exact (h 0) (by trivial)
  exact this htop

theorem haltsSet_not_isClosed_scott :
    ¬ @IsClosed (Topology.WithScott Trace) _ (HaltsSet) := by
  intro hClosed
  have hLower : IsLowerSet HaltsSet :=
    Topology.IsScott.isLowerSet_of_isClosed (α := Topology.WithScott Trace) (s := HaltsSet) hClosed
  have htop : (⊤ : Trace) ∈ HaltsSet := ⟨0, by trivial⟩
  have hbot : (⊥ : Trace) ∈ HaltsSet := hLower (bot_le : (⊥ : Trace) ≤ (⊤ : Trace)) htop
  rcases hbot with ⟨n, hn⟩
  cases hn

/--
No continuous total decider (to discrete `Bool`) can separate `Stabilizes` from its complement.

Topological reading:
the preimage of `{false}` would need to be Scott-open, but `StabilizesSet` is not Scott-open.
-/
theorem no_continuous_bool_decider_for_stabilizes :
    ¬ ∃ f : (Topology.WithScott Trace → Bool),
        Continuous f ∧ (∀ T, f T = false ↔ Stabilizes T) := by
  rintro ⟨f, hfCont, hf⟩
  have hFalseOpen : IsOpen ({false} : Set Bool) := isOpen_discrete _
  have hPreOpen : @IsOpen (Topology.WithScott Trace) _ (f ⁻¹' ({false} : Set Bool)) :=
    hfCont.isOpen_preimage _ hFalseOpen
  have hEq : (f ⁻¹' ({false} : Set Bool)) = StabilizesSet := by
    ext T
    constructor
    · intro hT
      have : f T = false := by simpa using hT
      exact (hf T).1 this
    · intro hT
      have : f T = false := (hf T).2 hT
      simpa [Set.mem_singleton_iff] using this
  have : @IsOpen (Topology.WithScott Trace) _ (StabilizesSet) := by
    simpa [hEq] using hPreOpen
  exact stabilizesSet_not_isOpen_scott this

/--
`WithScott Trace` has no nontrivial clopen subsets.

Intuition: in the Scott topology every nonempty closed set contains `⊥`, and any open set
containing `⊥` is `Set.univ` (because opens are upper and `⊥ ≤ x` for all `x`).
-/
theorem isOpen_isClosed_eq_empty_or_univ (s : Set Trace)
    (hsOpen : @IsOpen (Topology.WithScott Trace) _ s)
    (hsClosed : @IsClosed (Topology.WithScott Trace) _ s) :
    s = ∅ ∨ s = Set.univ := by
  by_cases hne : s.Nonempty
  · right
    have hLower : IsLowerSet s :=
      Topology.IsScott.isLowerSet_of_isClosed (α := Topology.WithScott Trace) (s := s) hsClosed
    rcases hne with ⟨x, hx⟩
    have hbot : (⊥ : Trace) ∈ s := hLower (bot_le : (⊥ : Trace) ≤ x) hx
    have hUpper : IsUpperSet s :=
      Topology.IsScott.isUpperSet_of_isOpen (α := Topology.WithScott Trace) (D := Set.univ) (s := s) hsOpen
    ext y
    constructor
    · intro _; trivial
    · intro _; exact hUpper (bot_le : (⊥ : Trace) ≤ y) hbot
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hne ⟨x, hx⟩

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.haltsSet_isUpper
#print axioms RevHalt.stabilizesSet_isLower
#print axioms RevHalt.haltsSet_dirSupInacc
#print axioms RevHalt.haltsSet_isOpen_scott
#print axioms RevHalt.stabilizesSet_eq_compl_haltsSet
#print axioms RevHalt.stabilizesSet_isClosed_scott
#print axioms RevHalt.stabilizesSet_not_isOpen_scott
#print axioms RevHalt.haltsSet_not_isClosed_scott
#print axioms RevHalt.no_continuous_bool_decider_for_stabilizes
#print axioms RevHalt.isOpen_isClosed_eq_empty_or_univ
