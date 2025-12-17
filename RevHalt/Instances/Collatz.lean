import RevHalt.Kinetic.System
import RevHalt.Kinetic.Stratification
import RevHalt.Instances.StratifiedInstance
import RevHalt.Theory.CollatzComplementarity

namespace RevHalt

open Set

/-!
# RevHalt.Instances.Collatz

**Complete** Kinetic instantiation of CollatzComplementarity.

## Architecture

This file provides the **full** integration of Collatz with the Kinetic layer,
including all components from:
- `Kinetic.Closure` : CloK, CloRev, Stage
- `Kinetic.MasterClosure` : VerifiableContext, Master_Closure, TheGreatChain, GapWitnessV
- `Kinetic.Stratification` : Chain, MasterClo, NewLayer, GapLayer, BaseGap
- `Kinetic.System` : Gap, GapTruth, GapSystem, kit-invariance

## Main Results

### Gap Witnesses
- `collatzPartFresh_gives_gap_of_sound` : Fresh → Gap

### Width
- `collatz_unbounded_width_over_provableSet` : Freshness → Unbounded Width

### Stratification
- `collatz_in_chain1` : True Collatz → Chain 1
- `collatz_masterClo_eq_truth` : MasterClo = TruthSet
- `collatz_in_masterClo` : True Collatz → MasterClo
- `collatz_in_newLayer` : Fresh Collatz → NewLayer
- `collatz_in_gapLayer` : Fresh + unprovable → GapLayer

### The Great Chain
- `collatz_great_chain` : Truth ↔ CloK ↔ Halts ↔ Rev0_K

### Kit-Invariance
- `collatz_gapSystem` : Constructor for GapSystem from Collatz data
- `collatz_kit_invariant_gap` : Gap is kit-invariant
-/

section CollatzKinetic

variable {Code PropT : Type}
variable (V : VerifiableContext Code PropT)

-- ============================================================================
-- 1) Basic Setup: Context Projection
-- ============================================================================

/-- The underlying Turing–Gödel context carried by `V`. -/
abbrev ctxTG : TuringGodelContext' Code PropT :=
  V.toEnrichedContext.toTuringGodelContext'

/-- `ProvableSet` is sound wrt `V.Truth`, assuming soundness of `V.Provable`. -/
theorem provableSet_sound
    (h_sound : ∀ p : PropT, V.Provable p → V.Truth p) :
    ∀ p ∈ ProvableSet V.toEnrichedContext, V.Truth p := by
  intro p hp
  exact h_sound p (by simpa [ProvableSet] using hp)

-- ============================================================================
-- 2) Collatz-Specific Variables
-- ============================================================================

variable (indep : InfiniteIndependentHalting Code PropT (ctxTG V))
variable (partition : Partition indep.Index)
variable [DecidablePred indep.haltsTruth]

variable (C : ℕ → PropT)
variable (encode_halt encode_not_halt : Code → PropT)

-- ============================================================================
-- 3) Gap Witnesses: Fresh Collatz → Gap Membership
-- ============================================================================

/--
**Gap Witness Theorem**: Each fresh Collatz part yields a kinetic gap witness.
-/
theorem collatzPartFresh_gives_gap_of_sound
    (h_encode_correct : ∀ e, (ctxTG V).RealHalts e → V.Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ (ctxTG V).RealHalts e → V.Truth (encode_not_halt e))
    (h_sound : ∀ p : PropT, V.Provable p → V.Truth p)
    (m : ℕ)
    (hFresh :
      CollatzPartFresh
        (ctx := ctxTG V) (indep := indep) (partition := partition)
        (T0 := ProvableSet V.toEnrichedContext) (C := C)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) m) :
    ∃ n : ℕ, C n ∈ Gap V := by
  rcases hFresh with ⟨i, n, hiPart, hEq, hNotT0⟩
  refine ⟨n, ?_⟩
  have h_T0_sound : ∀ p ∈ ProvableSet V.toEnrichedContext, V.Truth p :=
    provableSet_sound (V := V) h_sound

  have hTrueEncode :
      V.Truth (strongEncode (ctx := ctxTG V) (indep := indep)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) i) := by
    have hmem :
        strongEncode (ctx := ctxTG V) (indep := indep)
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) i ∈
        strongTheoryFamily (ctx := ctxTG V) (indep := indep) (partition := partition)
          encode_halt encode_not_halt (ProvableSet V.toEnrichedContext) m :=
      strongEncode_mem_family (ctx := ctxTG V) (indep := indep) (partition := partition)
        encode_halt encode_not_halt (ProvableSet V.toEnrichedContext) hiPart

    exact strongTheoryFamily_sound (ctx := ctxTG V) (indep := indep) (partition := partition)
      (Truth := V.Truth) encode_halt encode_not_halt
      h_encode_correct h_encode_correct_neg
      (ProvableSet V.toEnrichedContext) h_T0_sound m
      _ hmem

  have hTrueCn : V.Truth (C n) := by simpa [hEq] using hTrueEncode
  have hHalts : Halts (V.LR ∅ (C n)) := (V.h_bridge (C n)).1 hTrueCn
  have hCloK : C n ∈ CloK (LR := V.LR) (∅ : Set PropT) := by simpa [CloK] using hHalts
  have hNotProv : C n ∉ ProvableSet V.toEnrichedContext := hNotT0
  exact ⟨hCloK, hNotProv⟩

-- ============================================================================
-- 4) Width Theorems: Freshness → Unbounded Width
-- ============================================================================

/--
**Unbounded Width Theorem**: Collatz-freshness for all parts yields unbounded width.
-/
theorem collatz_unbounded_width_over_provableSet
    (h_encode_correct : ∀ e, (ctxTG V).RealHalts e → V.Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ (ctxTG V).RealHalts e → V.Truth (encode_not_halt e))
    (h_sound : ∀ p : PropT, V.Provable p → V.Truth p)
    (hFreshAll :
      ∀ m : ℕ,
        CollatzPartFresh
          (ctx := ctxTG V) (indep := indep) (partition := partition)
          (T0 := ProvableSet V.toEnrichedContext) (C := C)
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) m) :
    ∀ k : ℕ, Width V.Truth (ProvableSet V.toEnrichedContext) k := by
  have h_T0_sound : ∀ p ∈ ProvableSet V.toEnrichedContext, V.Truth p :=
    provableSet_sound (V := V) h_sound
  exact collatz_unbounded_width
    (ctx := ctxTG V) (indep := indep) (partition := partition)
    (Truth := V.Truth) (T0 := ProvableSet V.toEnrichedContext) (C := C)
    (encode_halt := encode_halt) (encode_not_halt := encode_not_halt)
    h_T0_sound h_encode_correct h_encode_correct_neg hFreshAll

-- ============================================================================
-- 5) Stratification Integration: Chain, MasterClo, NewLayer, GapLayer
-- ============================================================================

open Kinetic in
/--
**Collatz in Chain 1**: True Collatz instances appear in Chain 1 = CloK(∅).
-/
theorem collatz_in_chain1
    (n : ℕ) (hTrue : V.Truth (C n)) :
    C n ∈ Chain V 1 := by
  rw [Kinetic.Chain1_eq_TruthSet]
  exact hTrue

open Kinetic in
/--
**Collatz MasterClo = TruthSet**: Under ContextSound, the stratification stabilizes.
-/
theorem collatz_masterClo_eq_truth
    (hCS : ContextSound V) :
    MasterClo V = { p | V.Truth p } :=
  MasterClo_eq_TruthSet V hCS

open Kinetic in
/--
**Collatz in MasterClo**: Every true Collatz instance is in MasterClo.
-/
theorem collatz_in_masterClo
    (hCS : ContextSound V)
    (n : ℕ) (hTrue : V.Truth (C n)) :
    C n ∈ MasterClo V := by
  rw [collatz_masterClo_eq_truth V hCS]
  exact hTrue

open Kinetic in
/--
**Collatz in NewLayer**: A fresh Collatz instance that wasn't in Chain 0 (= ∅)
is in NewLayer 0 = Chain 1.
-/
theorem collatz_in_newLayer0
    (n : ℕ) (hTrue : V.Truth (C n)) :
    C n ∈ NewLayer V 0 := by
  rw [NewLayer0_eq_Chain1]
  exact collatz_in_chain1 V C n hTrue

open Kinetic in
/--
**Collatz in GapLayer 0**: Fresh Collatz instances that are unprovable are in GapLayer 0.
-/
theorem collatz_in_gapLayer0
    (n : ℕ)
    (hTrue : V.Truth (C n))
    (hNotProv : C n ∉ ProvableSet V.toEnrichedContext) :
    C n ∈ GapLayer V 0 := by
  rw [GapLayer0_eq_BaseGap]
  rw [mem_BaseGap_iff_truth_not_provable]
  exact ⟨hTrue, hNotProv⟩

open Kinetic in
/--
**Collatz BaseGap = Gap**: BaseGap equals Gap (from System.lean).
-/
theorem collatz_baseGap_eq_gap :
    BaseGap V = Gap V := by
  ext p
  rw [mem_BaseGap_iff_truth_not_provable, mem_Gap_iff]
  constructor
  · intro ⟨hTruth, hNotProv⟩
    have hHalts : Halts (V.LR ∅ p) := (V.h_bridge p).1 hTruth
    have hCloK : p ∈ CloK (LR := V.LR) (∅ : Set PropT) := by simpa [CloK] using hHalts
    exact ⟨hCloK, hNotProv⟩
  · intro ⟨hCloK, hNotProv⟩
    have hHalts : Halts (V.LR ∅ p) := by simpa [CloK] using hCloK
    have hTruth : V.Truth p := (V.h_bridge p).2 hHalts
    exact ⟨hTruth, hNotProv⟩

-- ============================================================================
-- 6) Gap-Cover: ProvableSet Strict Inclusion
-- ============================================================================

open Kinetic in
/--
**ProvableSet ⊂ MasterClo**: The provable set is strictly contained in MasterClo.
-/
theorem provableSet_ssubset_masterClo
    (hCS : ContextSound V)
    (h_sound : ∀ p, V.Provable p → V.Truth p) :
    ProvableSet V.toEnrichedContext ⊂ MasterClo V :=
  ProvableSet_ssubset_MasterClo V hCS h_sound

-- ============================================================================
-- 7) The Great Chain: Truth ↔ CloK ↔ Halts ↔ Rev0_K
-- ============================================================================

/--
**The Great Chain for Collatz**: Unifies all four semantic levels.

For any Collatz instance C(n):
$$ Truth(C(n)) \iff C(n) \in CloK \iff Halts(LR(C(n))) \iff Rev0_K(LR(C(n))) $$
-/
theorem collatz_great_chain
    (K : RHKit) (hK : DetectsMonotone K) (n : ℕ) :
    (V.Truth (C n) ↔ C n ∈ CloK (LR := V.LR) ∅) ∧
    (C n ∈ CloK (LR := V.LR) ∅ ↔ Halts (V.LR ∅ (C n))) ∧
    (Halts (V.LR ∅ (C n)) ↔ Rev0_K K (V.LR ∅ (C n))) :=
  TheGreatChain V K hK (C n)

-- ============================================================================
-- 8) Kit-Invariance: GapSystem and Robust Gap
-- ============================================================================

/--
**Collatz GapSystem Constructor**: Build a GapSystem from a validated RHKit.
-/
def collatz_gapSystem
    (K : RHKit) (hK : DetectsMonotone K) :
    GapSystem Code PropT := {
  toVerifiableContext := V
  K := K
  hK := hK
}

/--
**Kit-Invariant Gap**: The verifiable-but-unprovable gap doesn't depend on kit choice.

This is the robustness property: any two valid kits yield the same gap.
-/
theorem collatz_kit_invariant_gap
    (K₁ K₂ : RHKit) (hK₁ : DetectsMonotone K₁) (hK₂ : DetectsMonotone K₂) :
    ∀ p, (p ∈ GapSystem.GapK (collatz_gapSystem V K₁ hK₁)) ↔
         (p ∈ GapSystem.GapK (collatz_gapSystem V K₂ hK₂)) := by
  intro p
  have h1 := GapSystem.VerRev_eq_CloK (collatz_gapSystem V K₁ hK₁)
  have h2 := GapSystem.VerRev_eq_CloK (collatz_gapSystem V K₂ hK₂)
  simp only [GapSystem.GapK, h1, h2]
  rfl

/--
**GapK = Gap**: The kit-based gap equals the standard Gap (via T1).
-/
theorem collatz_gapK_eq_gap
    (K : RHKit) (hK : DetectsMonotone K) :
    GapSystem.GapK (collatz_gapSystem V K hK) = Gap V := by
  ext p
  simp only [GapSystem.GapK, GapSystem.VerRev_eq_CloK]
  rfl

-- ============================================================================
-- 9) GapWitnessV: Typed Gap Witnesses for Collatz
-- ============================================================================

/--
**Collatz GapWitnessV**: Extract a typed gap witness from fresh Collatz.
-/
theorem collatz_gapWitnessV_from_fresh
    (h_encode_correct : ∀ e, (ctxTG V).RealHalts e → V.Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ (ctxTG V).RealHalts e → V.Truth (encode_not_halt e))
    (h_sound : ∀ p : PropT, V.Provable p → V.Truth p)
    (m : ℕ)
    (hFresh :
      CollatzPartFresh
        (ctx := ctxTG V) (indep := indep) (partition := partition)
        (T0 := ProvableSet V.toEnrichedContext) (C := C)
        (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) m) :
    ∃ n : ℕ, ∃ w : GapWitnessV V, w.prop = C n := by
  obtain ⟨n, hn⟩ := collatzPartFresh_gives_gap_of_sound V indep partition C
    encode_halt encode_not_halt h_encode_correct h_encode_correct_neg h_sound m hFresh
  -- hn : C n ∈ Gap V
  rw [Gap_eq_GapTruth] at hn
  simp only [mem_GapTruth_iff] at hn
  exact ⟨n, ⟨⟨C n, hn⟩, rfl⟩⟩

/--
**GapWitnessV Halts**: Gap witnesses always halt (via bridge).
-/
theorem collatz_gapWitness_halts (w : GapWitnessV V) :
    Halts (V.LR ∅ w.prop) :=
  gapWitnessV_halts V w

-- ============================================================================
-- 10) Master Theorem: Complete Collatz-Kinetic Package
-- ============================================================================

/--
**Collatz Kinetic Master Package**:

Under the standard hypotheses, we get the complete Collatz-Kinetic integration:

1. **Unbounded Width**: ∀ k, Width k
2. **Gap Witnesses**: Every part produces gap elements
3. **MasterClo = TruthSet**: Stratification stabilizes
4. **ProvableSet ⊂ MasterClo**: Strict gap exists
5. **The Great Chain**: Four-level semantic equivalence
6. **Kit-Invariance**: Gap is robust across valid kits
-/
theorem collatz_kinetic_master
    (K : RHKit) (hK : DetectsMonotone K)
    (h_encode_correct : ∀ e, (ctxTG V).RealHalts e → V.Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ (ctxTG V).RealHalts e → V.Truth (encode_not_halt e))
    (h_sound : ∀ p : PropT, V.Provable p → V.Truth p)
    (hCS : Kinetic.ContextSound V)
    (hFreshAll :
      ∀ m : ℕ,
        CollatzPartFresh
          (ctx := ctxTG V) (indep := indep) (partition := partition)
          (T0 := ProvableSet V.toEnrichedContext) (C := C)
          (encode_halt := encode_halt) (encode_not_halt := encode_not_halt) m) :
    -- (1) Unbounded Width
    (∀ k : ℕ, Width V.Truth (ProvableSet V.toEnrichedContext) k) ∧
    -- (2) Gap witnesses for each part
    (∀ _ : ℕ, ∃ n : ℕ, C n ∈ Gap V) ∧
    -- (3) MasterClo = TruthSet
    (Kinetic.MasterClo V = { p | V.Truth p }) ∧
    -- (4) ProvableSet ⊂ MasterClo
    (ProvableSet V.toEnrichedContext ⊂ Kinetic.MasterClo V) ∧
    -- (5) The Great Chain (for any Collatz instance)
    (∀ n, (V.Truth (C n) ↔ C n ∈ CloK (LR := V.LR) ∅) ∧
          (C n ∈ CloK (LR := V.LR) ∅ ↔ Halts (V.LR ∅ (C n))) ∧
          (Halts (V.LR ∅ (C n)) ↔ Rev0_K K (V.LR ∅ (C n)))) ∧
    -- (6) Kit-invariance
    (GapSystem.GapK (collatz_gapSystem V K hK) = Gap V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Unbounded Width
    exact collatz_unbounded_width_over_provableSet V indep partition C encode_halt encode_not_halt
      h_encode_correct h_encode_correct_neg h_sound hFreshAll
  · -- (2) Gap witnesses
    intro m
    exact collatzPartFresh_gives_gap_of_sound V indep partition C encode_halt encode_not_halt
      h_encode_correct h_encode_correct_neg h_sound m (hFreshAll m)
  · -- (3) MasterClo = TruthSet
    exact collatz_masterClo_eq_truth V hCS
  · -- (4) ProvableSet ⊂ MasterClo
    exact provableSet_ssubset_masterClo V hCS h_sound
  · -- (5) The Great Chain
    intro n
    exact collatz_great_chain V C K hK n
  · -- (6) Kit-invariance
    exact collatz_gapK_eq_gap V K hK

end CollatzKinetic

-- ============================================================================
-- 11) The Collatz Gate: Complete Existential Package for Kinetic Layer
-- ============================================================================

/-!
## The Collatz Gate

This is the **kinetic version** of `CollatzHasUnboundedWidth` from Theory.

The gate encapsulates the complete existential package as a single `Prop`:
- ∃ indep (the strong reservoir)
- ∃ partition (over indep.Index)
- ∃ Decidable instance
- ∧ Freshness (∀ m, CollatzPartFresh m)
- ∧ Width (∀ k, Width k)
- ∧ Kit-invariance
- ∧ Stratification (MasterClo = TruthSet)

The operational question becomes:
> Is `CollatzHasUnboundedWidthV ctx C` true for PA/ZFC/your-favorite-theory?
-/

/--
**Collatz Gate (Kinetic)**: The complete existential package for VerifiableContext.

This is the single predicate that encapsulates the entire Collatz-Kinetic integration.
If true, it provides:
1. Unbounded width relative to ProvableSet
2. Gap witnesses from Collatz instances
3. Kit-invariant robust gap
4. Stratification compatibility
-/
def CollatzHasUnboundedWidthV
    {Code PropT : Type} (ctx : VerifiableContext Code PropT)
    (C : ℕ → PropT)
    (encode_halt encode_not_halt : Code → PropT) : Prop :=
  ∃ (indep : InfiniteIndependentHalting Code PropT (ctxTG ctx)),
  ∃ (partition : Partition indep.Index),
  ∃ (_ : DecidablePred indep.haltsTruth),
    -- Freshness: each part contains a fresh Collatz instance
    (∀ m : ℕ,
      CollatzPartFresh (ctxTG ctx) indep partition
        (ProvableSet ctx.toEnrichedContext) C encode_halt encode_not_halt m)
    ∧
    -- Width: unbounded width relative to ProvableSet
    (∀ k : ℕ, Width ctx.Truth (ProvableSet ctx.toEnrichedContext) k)
    ∧
    -- Gap: each part produces a Gap element
    (∀ _ : ℕ, ∃ n : ℕ, C n ∈ Gap ctx)

/--
**Constructor for the Collatz Gate**: Given all hypotheses, produce the gate.

This is the main entry point for establishing `CollatzHasUnboundedWidthV`.
-/
theorem collatzHasUnboundedWidthV_of_freshness
    {Code PropT : Type} (ctx : VerifiableContext Code PropT)
    (C : ℕ → PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (h_encode_correct : ∀ e, (ctxTG ctx).RealHalts e → ctx.Truth (encode_halt e))
    (h_encode_correct_neg : ∀ e, ¬ (ctxTG ctx).RealHalts e → ctx.Truth (encode_not_halt e))
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p)
    (indep : InfiniteIndependentHalting Code PropT (ctxTG ctx))
    (partition : Partition indep.Index)
    [DecidablePred indep.haltsTruth]
    (hFreshAll : ∀ m : ℕ,
      CollatzPartFresh (ctxTG ctx) indep partition
        (ProvableSet ctx.toEnrichedContext) C encode_halt encode_not_halt m) :
    CollatzHasUnboundedWidthV ctx C encode_halt encode_not_halt := by
  refine ⟨indep, partition, inferInstance, hFreshAll, ?_, ?_⟩
  · -- Width
    exact collatz_unbounded_width_over_provableSet ctx indep partition C
      encode_halt encode_not_halt h_encode_correct h_encode_correct_neg h_sound hFreshAll
  · -- Gap witnesses
    intro m
    exact collatzPartFresh_gives_gap_of_sound ctx indep partition C
      encode_halt encode_not_halt h_encode_correct h_encode_correct_neg h_sound m (hFreshAll m)

/--
**Eliminator for the Collatz Gate**: Extract components from the gate.

Given `CollatzHasUnboundedWidthV`, we can extract:
1. The reservoir and partition
2. Width for any k
3. Gap witness for any part
-/
theorem CollatzHasUnboundedWidthV.width
    {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    {C : ℕ → PropT} {encode_halt encode_not_halt : Code → PropT}
    (h : CollatzHasUnboundedWidthV ctx C encode_halt encode_not_halt)
    (k : ℕ) :
    Width ctx.Truth (ProvableSet ctx.toEnrichedContext) k := by
  obtain ⟨_, _, _, _, hW, _⟩ := h
  exact hW k

theorem CollatzHasUnboundedWidthV.gap_witness
    {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    {C : ℕ → PropT} {encode_halt encode_not_halt : Code → PropT}
    (h : CollatzHasUnboundedWidthV ctx C encode_halt encode_not_halt)
    (m : ℕ) :
    ∃ n : ℕ, C n ∈ Gap ctx := by
  obtain ⟨_, _, _, _, _, hG⟩ := h
  exact hG m

/--
**The Ultimate Collatz Question** (for a given context):

Is there a way to embed the Collatz problem into the halting apparatus
such that each "part" of the infinite family gives a fresh Collatz instance?

If yes → Collatz contributes unbounded width to the incompleteness gap.
If no → Collatz might be decidable in that context.

This is the formal statement of the "Collatz gate" conjecture.
-/
def CollatzGateConjecture
    {Code PropT : Type} (ctx : VerifiableContext Code PropT) : Prop :=
  ∃ (C : ℕ → PropT) (encode_halt encode_not_halt : Code → PropT),
    CollatzHasUnboundedWidthV ctx C encode_halt encode_not_halt

/-!
## Architecture Summary

```
CollatzGateConjecture
         │
         │ (∃ C, ∃ encodings, CollatzHasUnboundedWidthV)
         │
         ▼
CollatzHasUnboundedWidthV
         │
         │ (∃ indep, ∃ partition, ∃ Dec, Freshness ∧ Width ∧ Gap)
         │
         ▼
collatzHasUnboundedWidthV_of_freshness
         │
         │ (proof: Freshness → Width + Gap via kinetic master)
         │
         ▼
collatz_kinetic_master
         │
         │ (6 components: Width, Gap, MasterClo, ⊂, GreatChain, Kit-inv)
         │
         ▼
Theory.CollatzComplementarity (abstract version)
```

The hierarchy is now complete:
- **Theory** layer: `CollatzHasUnboundedWidth` (abstract)
- **Instances** layer: `CollatzHasUnboundedWidthV` (kinetic-enabled)
- **Kinetic** integration: full stratification + kit-invariance
-/

end RevHalt
