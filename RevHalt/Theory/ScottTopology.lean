import RevHalt.Theory.Stabilization
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order.ScottTopology

/-!
# RevHalt.Theory.ScottTopology

This file makes explicit the standard domain-theoretic / Scott-topological reading of the core
trace predicates **without** relying on the `IsOpen`/`IsClosed` wrappers for `Topology.WithScott`.

Rationale: in mathlib, the equivalence between `IsOpen` in the Scott topology and the usual
order-theoretic characterization (`IsUpperSet` + `DirSupInacc`) currently depends on
`Classical.choice`. Here we keep the development free of `Classical.choice` by working directly
with the order-theoretic predicates.

- `Halts` is **Scott-open** (Σ₁ / finitely observable): upper + directed-sup inaccessible.
- `Stabilizes` is **Scott-closed** (Π₁ / limit property): lower + directed-sup closed.

We also isolate the model-independent “discrete undecidability” obstruction:
Scott-compatible maps to discrete `Bool` cannot separate nontrivial predicates; they are forced
to be constant (`scottCompatibleToBool_const`).

Reference: `Mathlib.Topology.Order.ScottTopology` (definitions `DirSupInacc`, `DirSupClosed`,
and their `sSup` characterizations).
-/

namespace RevHalt

instance : CompleteLattice Trace := by
  delta Trace
  infer_instance

/-- The set of halting traces. -/
def HaltsSet : Set Trace := {T | Halts T}

/-- The set of stabilizing traces. -/
def StabilizesSet : Set Trace := {T | Stabilizes T}

/-! ### Order-theoretic Scott predicates (constructive) -/

/-- Scott-open (order-theoretic): upper set + inaccessible by directed suprema. -/
def IsScottOpen {α : Type*} [Preorder α] (s : Set α) : Prop := IsUpperSet s ∧ DirSupInacc s

/-- Scott-closed (order-theoretic): lower set + closed under directed suprema. -/
def IsScottClosed {α : Type*} [Preorder α] (s : Set α) : Prop := IsLowerSet s ∧ DirSupClosed s

/--
Order-theoretic surrogate for “continuity to discrete `Bool`”:
the preimages of the singletons `{true}` and `{false}` behave as Scott-clopen sets.

(In the actual Scott topology, continuity to a discrete space implies these conditions.
We state them explicitly here to avoid the `IsOpen`/`IsClosed` wrappers and their `Classical.choice`.)
-/
def ScottCompatibleToBool {α : Type*} [Preorder α] (f : α → Bool) : Prop :=
  IsScottOpen (f ⁻¹' ({true} : Set Bool)) ∧ IsScottClosed (f ⁻¹' ({true} : Set Bool)) ∧
    IsScottOpen (f ⁻¹' ({false} : Set Bool)) ∧ IsScottClosed (f ⁻¹' ({false} : Set Bool))

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

theorem haltsSet_isScottOpen : IsScottOpen HaltsSet :=
  ⟨haltsSet_isUpper, haltsSet_dirSupInacc⟩

theorem stabilizesSet_eq_compl_haltsSet : StabilizesSet = (HaltsSet)ᶜ := by
  ext T
  simp [StabilizesSet, HaltsSet, Stabilizes_iff_NotHalts]

theorem stabilizesSet_dirSupClosed : DirSupClosed StabilizesSet := by
  refine (dirSupClosed_iff_forall_sSup (α := Trace) (s := StabilizesSet)).2 ?_
  intro d _hdNonempty _hdDirected hdSubset n hn
  -- Show: `sSup d` stabilizes, since any witness at a finite stage would already appear in some `T ∈ d`.
  have hex : ∃ T : Trace, T ∈ d ∧ T n := (unary_relation_sSup_iff (s := d) (a := n)).1 hn
  rcases hex with ⟨T, hTd, hTn⟩
  have hStab : Stabilizes T := hdSubset hTd
  exact hStab n hTn

theorem stabilizesSet_isScottClosed : IsScottClosed StabilizesSet :=
  ⟨stabilizesSet_isLower, stabilizesSet_dirSupClosed⟩

theorem haltsSet_not_isScottClosed : ¬ IsScottClosed HaltsSet := by
  rintro ⟨hLower, _hClosed⟩
  have htop : (⊤ : Trace) ∈ HaltsSet := ⟨0, by trivial⟩
  have hbot : (⊥ : Trace) ∈ HaltsSet := hLower (bot_le : (⊥ : Trace) ≤ (⊤ : Trace)) htop
  rcases hbot with ⟨n, hn⟩
  cases hn

theorem stabilizesSet_not_isScottOpen : ¬ IsScottOpen StabilizesSet := by
  rintro ⟨hUpper, _hInacc⟩
  have hbot : (⊥ : Trace) ∈ StabilizesSet := by
    intro n hn
    cases hn
  have htop : (⊤ : Trace) ∈ StabilizesSet := hUpper (bot_le : (⊥ : Trace) ≤ (⊤ : Trace)) hbot
  have : ¬ Stabilizes (⊤ : Trace) := by
    intro h
    exact (h 0) (by trivial)
  exact this htop

/--
No Scott-compatible total decider (to discrete `Bool`) can recognize `Stabilizes`.

Topological reading:
the preimage of `{false}` would need to be Scott-open, but `StabilizesSet` is not Scott-open.
-/
theorem no_scottOpen_bool_decider_for_stabilizes :
    ¬ ∃ f : (Trace → Bool),
        IsScottOpen (f ⁻¹' ({false} : Set Bool)) ∧ (∀ T, f T = false ↔ Stabilizes T) := by
  rintro ⟨f, hScott, hf⟩
  have hEq : (f ⁻¹' ({false} : Set Bool)) = StabilizesSet := by
    ext T
    constructor
    · intro hT
      have : f T = false := by simpa using hT
      exact (hf T).1 this
    · intro hT
      have : f T = false := (hf T).2 hT
      simpa [Set.mem_singleton_iff] using this
  have : IsScottOpen StabilizesSet := by
    simpa [hEq] using hScott
  exact stabilizesSet_not_isScottOpen this

/--
Constructive "no nontrivial clopen":
if a set is Scott-open and Scott-closed and inhabited, then it is `Set.univ`.

Intuition: in the Scott topology every nonempty closed set contains `⊥`, and any open set
containing `⊥` is `Set.univ` (because opens are upper and `⊥ ≤ x` for all `x`).
-/
theorem isScottOpen_isScottClosed_nonempty_imp_univ {α : Type*} [Preorder α] [OrderBot α] (s : Set α)
    (hsOpen : IsScottOpen s)
    (hsClosed : IsScottClosed s) :
    s.Nonempty → s = Set.univ := by
  intro hne
  have hLower : IsLowerSet s := hsClosed.1
  rcases hne with ⟨x, hx⟩
  have hbot : (⊥ : α) ∈ s := hLower (bot_le : (⊥ : α) ≤ x) hx
  have hUpper : IsUpperSet s := hsOpen.1
  ext y
  constructor
  · intro _; trivial
  · intro _; exact hUpper (bot_le : (⊥ : α) ≤ y) hbot

/-- Constructive dual: if a Scott-open and Scott-closed set is not `Set.univ`, then it is empty. -/
theorem isScottOpen_isScottClosed_ne_univ_imp_empty {α : Type*} [Preorder α] [OrderBot α] (s : Set α)
    (hsOpen : IsScottOpen s)
    (hsClosed : IsScottClosed s) :
    s ≠ Set.univ → s = ∅ := by
  intro hneUniv
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  have : s = Set.univ :=
    isScottOpen_isScottClosed_nonempty_imp_univ s hsOpen hsClosed ⟨x, hx⟩
  exact hneUniv this

/-! ### Discrete undecidability as a Scott obstruction -/

/--
If a `Bool`-valued observable is Scott-compatible (in the sense above), it cannot perform a
nontrivial separation: it must be constant (hence equal to its value at `⊥`).
-/
theorem scottCompatibleToBool_const {α : Type*} [Preorder α] [OrderBot α]
    (f : α → Bool) (hf : ScottCompatibleToBool f) :
    ∀ x, f x = f ⊥ := by
  rcases hf with ⟨hTrueOpen, hTrueClosed, hFalseOpen, hFalseClosed⟩
  cases hbot : f (⊥ : α) with
  | false =>
      have hne : (f ⁻¹' ({false} : Set Bool)).Nonempty := by
        refine ⟨(⊥ : α), ?_⟩
        simp [Set.preimage, hbot]
      have hUniv :
          (f ⁻¹' ({false} : Set Bool)) = Set.univ :=
        isScottOpen_isScottClosed_nonempty_imp_univ
          (s := (f ⁻¹' ({false} : Set Bool)))
          hFalseOpen hFalseClosed hne
      intro x
      have hxMem : x ∈ (f ⁻¹' ({false} : Set Bool)) := by
        simp [hUniv]
      have hx : f x = false := by
        simpa [Set.preimage, Set.mem_singleton_iff] using hxMem
      simp [hx]
  | true =>
      have hne : (f ⁻¹' ({true} : Set Bool)).Nonempty := by
        refine ⟨(⊥ : α), ?_⟩
        simp [Set.preimage, hbot]
      have hUniv :
          (f ⁻¹' ({true} : Set Bool)) = Set.univ :=
        isScottOpen_isScottClosed_nonempty_imp_univ
          (s := (f ⁻¹' ({true} : Set Bool)))
          hTrueOpen hTrueClosed hne
      intro x
      have hxMem : x ∈ (f ⁻¹' ({true} : Set Bool)) := by
        simp [hUniv]
      have hx : f x = true := by
        simpa [Set.preimage, Set.mem_singleton_iff] using hxMem
      simp [hx]

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.haltsSet_isUpper
#print axioms RevHalt.stabilizesSet_isLower
#print axioms RevHalt.haltsSet_dirSupInacc
#print axioms RevHalt.stabilizesSet_eq_compl_haltsSet
#print axioms RevHalt.haltsSet_isScottOpen
#print axioms RevHalt.stabilizesSet_dirSupClosed
#print axioms RevHalt.stabilizesSet_isScottClosed
#print axioms RevHalt.haltsSet_not_isScottClosed
#print axioms RevHalt.stabilizesSet_not_isScottOpen
#print axioms RevHalt.no_scottOpen_bool_decider_for_stabilizes
#print axioms RevHalt.isScottOpen_isScottClosed_nonempty_imp_univ
#print axioms RevHalt.isScottOpen_isScottClosed_ne_univ_imp_empty
#print axioms RevHalt.scottCompatibleToBool_const
