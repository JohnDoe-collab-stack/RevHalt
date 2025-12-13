/-
  RevHalt.Unified.Coded.Context

  Builds a coded Turing-Gödel context from RigorousModel + SoundLogicEncodedCoded.

  ## Key Difference from Original

  The `diagonal_program_coded` field only provides diagonalization for
  coded formula families (g : FC.GCode), not arbitrary G : Code → PropT.

  This is sufficient for the incompleteness theorems because the actual
  formulas used in the proofs are always arithmetically definable.
-/
import RevHalt.Unified.Coded.Interface

namespace RevHalt_Unified.Coded
open RevHalt_Unified

/-- Coded version of TuringGodelContext'.
    Diagonalization is restricted to coded formula families. -/
structure TuringGodelContextCoded (Code PropT : Type) (FC : FamilyCoding Code PropT) where
  RealHalts : Code → Prop
  Provable : PropT → Prop
  Truth : PropT → Prop
  Not : PropT → PropT
  FalseT : PropT
  consistent : ¬Provable FalseT
  absurd : ∀ p, Provable p → Provable (Not p) → Provable FalseT
  truth_not_iff : ∀ p, Truth (Not p) ↔ ¬Truth p

  /-- Diagonal diagonalization for coded families only. -/
  diagonal_program_coded :
    ∀ g : FC.GCode, ∃ e : Code, RealHalts e ↔ Provable (Not (FC.evalG g e))

/-- Build TuringGodelContextCoded from M + K + SoundLogicEncodedCoded. -/
def TGContextCoded_from_RM
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT) :
    TuringGodelContextCoded M.Code PropT Lenc.FC where
  RealHalts := fun e => Rev0_K K (rmCompile M e)
  Provable := Lenc.Logic.Provable
  Truth := Lenc.Logic.Truth
  Not := Lenc.Logic.Not
  FalseT := Lenc.Logic.FalseP
  consistent := Lenc.Logic.consistent
  absurd := Lenc.Logic.absurd
  truth_not_iff := Lenc.Logic.truth_not_iff
  diagonal_program_coded := by
    intro g
    -- (1) Obtain pc that defines Provable(Not(evalG g e))
    obtain ⟨pc, hpc⟩ := Lenc.Arith.repr_provable_not_coded g
    -- (2) diagonal_halting of M on pc
    obtain ⟨e, he⟩ := M.diagonal_halting pc
    use e
    -- (3) Convert RealHalts via T1_traces + rm_compile_halts_equiv
    -- RealHalts e = Rev0_K K (rmCompile M e)
    -- We need: Rev0_K K (rmCompile M e) ↔ Provable (Not (evalG g e))
    have hR : Rev0_K K (rmCompile M e) ↔ RMHalts M e := by
      rw [T1_traces K hK (rmCompile M e)]
      exact rm_compile_halts_equiv M e
    -- he : RMHalts M e ↔ PredDef pc e
    -- hpc : PredDef pc e ↔ Provable (Not (evalG g e))
    exact hR.trans (he.trans (hpc e))

/-- Enriched coded context with H (halting formula). -/
structure EnrichedContextCoded (Code PropT : Type) (FC : FamilyCoding Code PropT) extends
    TuringGodelContextCoded Code PropT FC where
  /-- Halting formula -/
  H : Code → PropT
  /-- H e is true iff e halts -/
  h_truth_H : ∀ e, RealHalts e ↔ Truth (H e)

/-- Build EnrichedContextCoded from M + K + SoundLogicEncodedCoded. -/
def EnrichedContextCoded_from_RM
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (Lenc : SoundLogicEncodedCoded M PropT) :
    EnrichedContextCoded M.Code PropT Lenc.FC where
  toTuringGodelContextCoded := TGContextCoded_from_RM M K hK Lenc
  H := Lenc.HaltE.HaltEncode
  h_truth_H := by
    intro e
    -- RealHalts e = Rev0_K K (rmCompile M e)
    -- Need: Rev0_K K (rmCompile M e) ↔ Truth (HaltEncode e)
    have hR : Rev0_K K (rmCompile M e) ↔ RMHalts M e := by
      rw [T1_traces K hK (rmCompile M e)]
      exact rm_compile_halts_equiv M e
    exact hR.trans (Lenc.HaltE.encode_correct e)

end RevHalt_Unified.Coded
