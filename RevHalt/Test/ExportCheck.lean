-- RevHalt/Test/ExportCheck.lean
-- Comprehensive check that all main exports are accessible

import RevHalt.Main

namespace RevHalt.Test.ExportCheck

open RevHalt

-- ============================================================================
-- BASE LAYER EXPORTS
-- ============================================================================

section BaseExports
  #check Trace
  #check Halts
  #check up
  #check up_mono
  #check exists_up_iff
  #check RHKit
  #check DetectsMonotone
  #check Rev_K
  #check Rev0_K
end BaseExports

-- ============================================================================
-- THEORY LAYER EXPORTS
-- ============================================================================

section TheoryExports
  -- T1 Canonicity
  #check T1_traces
  #check T1_uniqueness
  #check T1_semantics

  -- Semantic Bridge
  #check ModE
  #check ThE
  #check CloE
  #check SemConsequences
  #check DynamicBridge
  #check verdict_K

  -- T2 Impossibility
  #check TuringGodelContext'
  #check InternalHaltingPredicate
  #check T2_impossibility

  -- T3 Complementarity
  #check T3_weak_extension
  #check InfiniteIndependentHalting
  #check Partition
  #check T3_strong
end TheoryExports

-- ============================================================================
-- KINETIC LAYER EXPORTS
-- ============================================================================

section KineticExports
  #check CloK
  #check CloRev
  #check Stage
  #check mem_CloK_iff
  #check CloRev_mem_iff_CloK_mem

  #check VerifiableContext
  #check Master_Closure
  #check Truth_is_CloK
  #check TheGreatChain

  #check Gap
  #check GapTruth
  #check GapSystem
  #check gap_nonempty
  #check independent_witness
end KineticExports

-- ============================================================================
-- ORACLE LAYER EXPORTS
-- ============================================================================

section OracleExports
  #check TruthOracle
  #check InternalizesOracle
  #check oracle_not_internalizable
  #check bridge_is_oracular
  #check oracle_authority_is_gap
end OracleExports

-- ============================================================================
-- BRIDGE LAYER EXPORTS
-- ============================================================================

section BridgeExports
  -- RigorousModel
  #check RigorousModel
  #check RMHalts
  #check rmCompile
  #check SoundLogicDef
  #check Arithmetization
  #check TGContext_from_RM
  #check RevHalt_Master_Rigorous

  -- Context
  #check EnrichedContext
  #check ProvableSet
  #check true_but_unprovable_exists
  #check independent_code_exists
  #check strict_extension

  -- Master
  #check SoundLogicEncoded
  #check EnrichedContext_from_Encoded
  #check RevHalt_Master_Complete
end BridgeExports

-- ============================================================================
-- CODED LAYER EXPORTS
-- ============================================================================

section CodedExports
  #check Coded.FamilyCoding
  #check Coded.ArithmetizationCoded
  #check Coded.HaltingEncoding
  #check Coded.SoundLogicEncodedCoded
  #check Coded.TuringGodelContextCoded
  #check Coded.EnrichedContextCoded
  #check Coded.RevHalt_Master_Complete_Coded
  #check Coded.Master_Coded_T2prime
  #check Coded.Master_Coded_T2
  #check Coded.Master_Coded_Full
end CodedExports

-- ============================================================================
-- EXTENSIONS EXPORTS
-- ============================================================================

section ExtensionsExports
  open Extensions.OmegaChaitin in
  #check OmegaRefSystem

  #check RefSystem
  #check RefSystem.LR_ref
  #check RefSystem.DynamicBridge_ref
  #check RefSystem.DR0_ref
  #check RefSystem.DR1_ref
end ExtensionsExports

-- ============================================================================
-- INSTANCES EXPORTS
-- ============================================================================

section InstancesExports
  open Instances.Arithmetization in
  #check PRModel

  open Instances.Arithmetization in
  #check PRModel_Master_Theorem

  open Instances.PA in
  #check PA_Master_Theorem
end InstancesExports

-- ============================================================================
-- SUCCESS MESSAGE
-- ============================================================================

#print "✅ ALL EXPORTS VERIFIED - No information lost!"

end RevHalt.Test.ExportCheck
