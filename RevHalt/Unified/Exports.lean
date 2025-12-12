-- RevHalt/Unified/Exports.lean
-- Explicit public API surface for RevHalt.Unified

import RevHalt.Unified.Core
import RevHalt.Unified.RigorousModel
import RevHalt.Unified.Bridge

/-!
# RevHalt Unified Exports

This file explicitly lists the public API surface.
Only symbols exported here are considered stable.
-/

-- Export explicite: uniquement ce qui est garanti comme API publique.
export RevHalt_Unified (
  -- Core (T1/T2/T3 framework from RevHalt.lean)
  -- Note: Trace, Halts, RHKit etc. come from RevHalt.lean directly

  -- EnrichedContext (from Core)
  EnrichedContext ProvableSet
  true_but_unprovable_exists independent_code_exists
  encoding_cannot_be_complete undecidable_code_exists
  strict_extension strict_extension'
  ProvableSet_sound

  -- Rigorous model layer (M/L/A from RigorousModel)
  RigorousModel RMHalts rmCompile rm_compile_halts_equiv
  rm_diagonal_def no_anti_halting
  SoundLogicDef Arithmetization
  TGContext_from_RM RevHalt_Master_Rigorous

  -- Bridge layer (M/L/A/E from Bridge)
  SoundLogicEncoded EnrichedContext_from_Encoded
  RealHalts_eq_Halts RealHalts_encoded_simp
  Provable_encoded_simp Truth_encoded_simp Not_encoded_simp
  FalseT_encoded_simp H_encoded_simp ProvableSet_mem
  strict_extension_sound RevHalt_Master_Complete
)
