import RevHalt.Unified.Core
import RevHalt.Unified.RigorousModel

namespace RevHalt_Unified

/-!
# Bridge: connecting RigorousModel to the T1-T2-T3 Master Chain

This file closes the loop by enriching `SoundLogicDef` with a halting encoding,
allowing us to build an `EnrichedContext` and prove the final Master Theorem.

## Hypothesis Classification (M/L/A/E)

| Component | Structure | Key Fields |
|-----------|-----------|------------|
| **M** (Computability) | `RigorousModel` | `Code`, `Program`, `PredCode`, `PredDef`, `diagonal_halting`, `no_complement_halts` |
| **L** (Logic) | `SoundLogicDef PropT` | `Provable`, `Truth`, `soundness`, `Not`, `FalseP`, `consistent`, `absurd`, `truth_not_iff` |
| **A** (Arithmetization) | `Arithmetization M PropT L` | `repr_provable_not` |
| **E** (Encoding) | (in `SoundLogicEncoded`) | `HaltEncode`, `encode_correct` |

## Requirements by Theorem

### T2 (Existence of unprovable truth)
- **Required**: M + L (consistency, absurd) + A (repr_provable_not via diagonal_halting)
- **Proven by**: `true_but_unprovable_exists`

### T2' (Independence: ¬Provable(H e) ∧ ¬Provable(¬H e))
- **Required**: M + L (+ soundness) + A + E (encode_correct)
- **Proven by**: `independent_code_exists`

### T3 (Sound extension of provable set)
- **Required**: T2 result + L.soundness
- **Proven by**: `strict_extension_sound`

## Instantiation Guide

To instantiate the framework, provide:
1. A `RigorousModel` with `diagonal_halting` and `no_complement_halts`
2. A `SoundLogicDef PropT` with all 8 fields
3. An `Arithmetization` with `repr_provable_not`
4. A `HaltEncode` function with `encode_correct`

Bundle into `SoundLogicEncoded`, then call `RevHalt_Master_Complete`.
-/

/--
**Strict Sound Extension (T3)**
Theorem: The set of provable truths can be strictly extended while preserving soundness.
-/
theorem strict_extension_sound {Code PropT : Type} (ctx : EnrichedContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∃ T1 : Set PropT, ProvableSet ctx ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p) := by
  obtain ⟨p, h_true, h_not_prov⟩ := true_but_unprovable_exists ctx
  have h_sound_T0 : ∀ q ∈ ProvableSet ctx, ctx.Truth q := fun q hq => h_sound q hq
  have h_fresh : p ∉ ProvableSet ctx := h_not_prov
  use ProvableSet ctx ∪ {p}
  constructor
  · constructor
    · exact Set.subset_union_left
    · intro h_eq; exact h_fresh (h_eq (Set.mem_union_right (ProvableSet ctx) rfl))
  · intro q hq
    rcases hq with h_in | h_eq
    · exact h_sound_T0 q h_in
    · rw [h_eq]; exact h_true

/--
**Sound Logic with Halting Encoding** (Full Package)
Bundles: Logic (L) + Arithmetization (A) + HaltEncode (E).
This is the final requirement for T2 and T3.
-/
structure SoundLogicEncoded (M : RigorousModel) (PropT : Type) where
  /-- Pure Logic -/
  Logic : SoundLogicDef PropT
  /-- Arithmetization (links M and Logic) -/
  Arith : Arithmetization M PropT Logic
  /-- Halting Encoding: The logic can express "e halts" -/
  HaltEncode : M.Code → PropT
  /-- Semantic correctness of HaltEncode -/
  encode_correct : ∀ e, RMHalts M e ↔ Logic.Truth (HaltEncode e)

/--
**Bridge to EnrichedContext**
Constructs the full `EnrichedContext` needed for the Master Theorem.
-/
def EnrichedContext_from_Encoded
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) :
    EnrichedContext M.Code PropT :=
  let ctxTG := TGContext_from_RM M K hK L.Logic L.Arith
  {
    toTuringGodelContext' := ctxTG
    Truth := L.Logic.Truth
    H := L.HaltEncode
    h_truth_H := by
      intro e
      change Rev0_K K (rmCompile M e) ↔ L.Logic.Truth (L.HaltEncode e)
      rw [T1_traces K hK (rmCompile M e)]
      rw [rm_compile_halts_equiv M e]
      exact L.encode_correct e
    truth_not_iff := L.Logic.truth_not_iff
  }

/--
**Utility**: Direct link between RealHalts and concrete execution.
-/
theorem RealHalts_eq_Halts
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) :
    let ctx := EnrichedContext_from_Encoded M K hK L
    ∀ e, ctx.RealHalts e ↔ Halts (rmCompile M e) := by
  intro _ e
  show Rev0_K K (rmCompile M e) ↔ Halts (rmCompile M e)
  exact T1_traces K hK (rmCompile M e)

/-- Simp lemma: RealHalts in the constructed context is just standard Halts. -/
@[simp] theorem RealHalts_encoded_simp
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT)
    (e : M.Code) :
    (EnrichedContext_from_Encoded M K hK L).RealHalts e ↔ Halts (rmCompile M e) := by
  show Rev0_K K (rmCompile M e) ↔ Halts (rmCompile M e)
  exact T1_traces K hK (rmCompile M e)

-- ==============================================================================================
-- Simp lemmas for ergonomic proofs
-- ==============================================================================================

@[simp] theorem Provable_encoded_simp
    {PropT : Type} (M : RigorousModel) (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) (p : PropT) :
    (EnrichedContext_from_Encoded M K hK L).Provable p ↔ L.Logic.Provable p := Iff.rfl

@[simp] theorem Truth_encoded_simp
    {PropT : Type} (M : RigorousModel) (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) (p : PropT) :
    (EnrichedContext_from_Encoded M K hK L).Truth p ↔ L.Logic.Truth p := Iff.rfl

@[simp] theorem Not_encoded_simp
    {PropT : Type} (M : RigorousModel) (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) (p : PropT) :
    (EnrichedContext_from_Encoded M K hK L).Not p = L.Logic.Not p := rfl

@[simp] theorem FalseT_encoded_simp
    {PropT : Type} (M : RigorousModel) (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) :
    (EnrichedContext_from_Encoded M K hK L).FalseT = L.Logic.FalseP := rfl

@[simp] theorem H_encoded_simp
    {PropT : Type} (M : RigorousModel) (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) (e : M.Code) :
    (EnrichedContext_from_Encoded M K hK L).H e = L.HaltEncode e := rfl

@[simp] theorem ProvableSet_mem
    {Code PropT : Type} (ctx : EnrichedContext Code PropT) (p : PropT) :
    p ∈ ProvableSet ctx ↔ ctx.Provable p := Iff.rfl

/--
**FINAL COMPLETE MASTER THEOREM**
Proves T2 (True but unprovable), T2' (Independence), and T3 (Sound Extension)
strictly from the RigorousModel and SoundLogicEncoded.

1. **True w/o Proof**: ∃ p, Truth p ∧ ¬Provable p
2. **Independence**: ∃ e, ¬Provable (H e) ∧ ¬Provable (Not (H e))
3. **Sound Extension**: ProvableSet can be strictly extended preserving Truth
-/
theorem RevHalt_Master_Complete
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT) :
    let ctx := EnrichedContext_from_Encoded M K hK L
    -- (1) T1 equivalent: RealHalts matches Model Execution
    (∀ e, ctx.RealHalts e ↔ Halts (rmCompile M e)) ∧
    -- (2) T2: True w/o Proof
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    -- (3) T2': Independence
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) ∧
    -- (4) T3: Strict Sound Extension
    (∃ T1 : Set PropT, ProvableSet ctx ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p)) := by
  let ctx := EnrichedContext_from_Encoded M K hK L
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) T1: use stable simp lemma, targeted via ctx
    intro e
    set_option linter.unnecessarySimpa false in
    simpa [ctx] using RealHalts_encoded_simp (M := M) (K := K) (hK := hK) (L := L) e
  · -- (2) T2
    exact true_but_unprovable_exists ctx
  · -- (3) T2'
    exact independent_code_exists ctx L.Logic.soundness
  · -- (4) T3
    obtain ⟨T1, h_strict, h_sound⟩ := strict_extension_sound ctx L.Logic.soundness
    use T1, h_strict, h_sound

end RevHalt_Unified
