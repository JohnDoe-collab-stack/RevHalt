/-
  RevHalt.Unified.Coded.Master

  Coded versions of T1/T2/T2'/T3 theorems.

  ## Key Observation

  The proofs of T2/T2'/T3 only use the diagonal program for specific
  formula families that are themselves arithmetically definable.
  Therefore, restricting to coded families loses no generality.

  The theorems here are "coded" analogues of the original T1/T2/T3.
-/
import RevHalt.Unified.Coded.Context

namespace RevHalt_Unified.Coded
open RevHalt_Unified

variable {Code PropT : Type}

-- ==============================================================================================
-- ProvableSet for coded context
-- ==============================================================================================

/-- ProvableSet for coded context. -/
def ProvableSetCoded {FC : FamilyCoding Code PropT}
    (ctx : EnrichedContextCoded Code PropT FC) : Set PropT :=
  {p | ctx.Provable p}

-- ==============================================================================================
-- Master Theorem (Coded Version) - Minimal T1 + Diagonal
-- ==============================================================================================

/-- **MASTER THEOREM (CODED) - Version 1**

    Proves T1 + Diagonal for H_code.
    This is the minimal version that can be instantiated with real logics like PA.

    Requirements:
    - `H_code : FC.GCode` - a code for the halting formula family
    - `hH_code` - proof that evalG H_code e = HaltEncode e -/
theorem RevHalt_Master_Complete_Coded
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT)
    -- Assuming H is part of a coded family
    (H_code : Lenc.FC.GCode)
    (hH_code : ∀ e, Lenc.FC.evalG H_code e = Lenc.HaltE.HaltEncode e) :
    let ctx := EnrichedContextCoded_from_RM M K hK Lenc
    -- (1) T1: RealHalts matches Truth of H
    (∀ e, ctx.RealHalts e ↔ ctx.Truth (ctx.H e)) ∧
    -- (2) Diagonal for H_code: ∃ e, RealHalts e ↔ Provable (Not (H e))
    (∃ e, ctx.RealHalts e ↔ ctx.Provable (ctx.Not (ctx.H e))) := by
  let ctx := EnrichedContextCoded_from_RM M K hK Lenc
  constructor
  · -- (1) T1: Direct from h_truth_H
    intro e
    exact ctx.h_truth_H e
  · -- (2) Diagonal for H_code
    obtain ⟨e, he⟩ := ctx.diagonal_program_coded H_code
    use e
    simp only [hH_code] at he
    exact he

-- ==============================================================================================
-- Extended Master (T2/T2'/T3) - Simplified version with less nesting
-- ==============================================================================================

/-- **MASTER THEOREM (CODED) - Version 2 (T2' only, cleanest)**

    The cleanest result: given soundness, there exists an independent code.

    This is the core incompleteness result for coded families. -/
theorem Master_Coded_T2prime
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT)
    (H_code : Lenc.FC.GCode)
    (hH_code : ∀ e, Lenc.FC.evalG H_code e = Lenc.HaltE.HaltEncode e)
    (h_sound : ∀ p, Lenc.Logic.Provable p → Lenc.Logic.Truth p) :
    let ctx := EnrichedContextCoded_from_RM M K hK Lenc
    -- T2': Independent code exists
    ∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e)) := by
  let ctx := EnrichedContextCoded_from_RM M K hK Lenc
  obtain ⟨e, he⟩ := ctx.diagonal_program_coded H_code
  simp only [hH_code] at he
  use e
  constructor
  · -- ¬Provable (H e)
    intro hProv
    -- If Provable (H e), then Truth (H e) by soundness
    have hTrue : ctx.Truth (ctx.H e) := h_sound _ hProv
    -- So RealHalts e by h_truth_H
    have hHalt : ctx.RealHalts e := ctx.h_truth_H e |>.mpr hTrue
    -- By diagonal: Provable (Not (H e))
    have hProvNot : ctx.Provable (ctx.Not (ctx.H e)) := he.mp hHalt
    -- By absurd: Provable FalseT
    exact ctx.consistent (ctx.absurd _ hProv hProvNot)
  · -- ¬Provable (Not (H e))
    intro hProvNot
    -- By diagonal: RealHalts e
    have hHalt : ctx.RealHalts e := he.mpr hProvNot
    -- By h_truth_H: Truth (H e)
    have hTrue : ctx.Truth (ctx.H e) := ctx.h_truth_H e |>.mp hHalt
    -- If Provable (Not (H e)), then Truth (Not (H e)) by soundness
    have hTrueNot : ctx.Truth (ctx.Not (ctx.H e)) := h_sound _ hProvNot
    -- But Truth (Not (H e)) = ¬Truth (H e)
    rw [ctx.truth_not_iff] at hTrueNot
    exact hTrueNot hTrue

/-- **T2 from T2'**: True but unprovable exists.

    Uses the independent code to extract a true unprovable proposition. -/
theorem Master_Coded_T2
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT)
    (H_code : Lenc.FC.GCode)
    (hH_code : ∀ e, Lenc.FC.evalG H_code e = Lenc.HaltE.HaltEncode e)
    (h_sound : ∀ p, Lenc.Logic.Provable p → Lenc.Logic.Truth p) :
    let ctx := EnrichedContextCoded_from_RM M K hK Lenc
    -- T2: True but unprovable exists
    ∃ p, ctx.Truth p ∧ ¬ctx.Provable p := by
  let ctx := EnrichedContextCoded_from_RM M K hK Lenc
  obtain ⟨e, hNotProvH, hNotProvNotH⟩ :=
    Master_Coded_T2prime M K hK Lenc H_code hH_code h_sound
  -- We have ¬Provable (H e) and ¬Provable (Not (H e))
  -- Case on whether e halts
  by_cases hHalt : ctx.RealHalts e
  · -- e halts → Truth (H e) is true, and ¬Provable (H e)
    use ctx.H e
    constructor
    · exact ctx.h_truth_H e |>.mp hHalt
    · exact hNotProvH
  · -- e doesn't halt → Truth (Not (H e)) is true, and ¬Provable (Not (H e))
    use ctx.Not (ctx.H e)
    constructor
    · rw [ctx.truth_not_iff]
      rw [← ctx.h_truth_H]
      exact hHalt
    · exact hNotProvNotH

/-- **Full Master (Coded)**: T1 + Diagonal + T2 + T2'.

    Combines all results with soundness hypothesis. -/
theorem Master_Coded_Full
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT)
    (H_code : Lenc.FC.GCode)
    (hH_code : ∀ e, Lenc.FC.evalG H_code e = Lenc.HaltE.HaltEncode e)
    (h_sound : ∀ p, Lenc.Logic.Provable p → Lenc.Logic.Truth p) :
    let ctx := EnrichedContextCoded_from_RM M K hK Lenc
    -- (1) T1: RealHalts matches Truth of H
    (∀ e, ctx.RealHalts e ↔ ctx.Truth (ctx.H e)) ∧
    -- (2) Diagonal for H_code
    (∃ e, ctx.RealHalts e ↔ ctx.Provable (ctx.Not (ctx.H e))) ∧
    -- (3) T2: True but unprovable exists
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    -- (4) T2': Independent code exists
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) := by
  let ctx := EnrichedContextCoded_from_RM M K hK Lenc
  have ⟨h1, h2⟩ := RevHalt_Master_Complete_Coded M K hK Lenc H_code hH_code
  refine ⟨h1, h2, ?_, ?_⟩
  · exact Master_Coded_T2 M K hK Lenc H_code hH_code h_sound
  · exact Master_Coded_T2prime M K hK Lenc H_code hH_code h_sound

end RevHalt_Unified.Coded
