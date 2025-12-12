import RevHalt.Unified.Core
import RevHalt.Unified.RigorousModel

namespace RevHalt_Unified

/-!
# Bridge: connecting RigorousModel to the T1-T2-T3 Master Chain

This file closes the loop by enriching `SoundLogicDef` with a halting encoding,
allowing us to build an `EnrichedContext` and prove the final Master Theorem.
-/

/--
**Strict Sound Extension (T3)**
Theorem: The set of provable truths can be strictly extended while preserving soundness.
Retrieved from previous improvements and adapted for SoundLogicEncoded.
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
**Sound Logic with Halting Encoding**
Extends `SoundLogicDef` with the ability to express "program e halts".
This is the final requirement for T2 and T3.
-/
structure SoundLogicEncoded (M : RigorousModel) (PropT : Type) extends SoundLogicDef M PropT where
  /-- Halting Encoding: The logic can express "e halts" -/
  HaltEncode : M.Code → PropT
  /-- Semantic correctness of HaltEncode -/
  encode_correct : ∀ e, RMHalts M e ↔ Truth (HaltEncode e)

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
  let ctxTG := TGContext_from_RM M K hK L.toSoundLogicDef
  {
    toTuringGodelContext' := ctxTG
    Truth := L.Truth
    H := L.HaltEncode
    h_truth_H := by
      intro e
      -- Robust proof: explicitly change goal to underlying definition
      -- ctxTG.RealHalts e = Rev0_K K (rmCompile M e)
      change Rev0_K K (rmCompile M e) ↔ L.Truth (L.HaltEncode e)
      rw [T1_traces K hK (rmCompile M e)]
      rw [rm_compile_halts_equiv M e]
      exact L.encode_correct e
    truth_not_iff := L.truth_not_iff
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
  intro ctx e
  simpa using (T1_traces K hK (rmCompile M e))

/-- Simp lemma: RealHalts in the constructed context is just standard Halts. -/
@[simp] theorem RealHalts_encoded_simp
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicEncoded M PropT)
    (e : M.Code) :
    (EnrichedContext_from_Encoded M K hK L).RealHalts e ↔ Halts (rmCompile M e) := by
  simpa using (T1_traces K hK (rmCompile M e))

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
  · -- (1) T1
    intro e
    exact T1_traces K hK (rmCompile M e)
  · -- (2) T2
    exact true_but_unprovable_exists ctx
  · -- (3) T2'
    exact independent_code_exists ctx L.soundness
  · -- (4) T3
    obtain ⟨T1, h_strict, h_sound⟩ := strict_extension_sound ctx L.soundness
    use T1, h_strict, h_sound

end RevHalt_Unified
