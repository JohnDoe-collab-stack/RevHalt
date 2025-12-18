-- RevHalt/Test/CoreCheck.lean
-- Check that core theorems are accessible

import RevHalt.Main

open RevHalt

-- Core theorems
#check @T1_traces
#check @T1_uniqueness
#check @T2_impossibility
#check @T3_strong
#check @T3_weak_extension

-- Key structures
#check @RHKit
#check @ImpossibleSystem
#check @RigorousModel
#check @EnrichedContext
#check @SoundLogicEncoded

-- Master theorem
#check @RevHalt_Master_Complete

-- Coded versions exist
#check @Coded.RevHalt_Master_Complete_Coded
#check @Coded.Master_Coded_Full

-- Kinetic
#check @CloK
#check @VerifiableContext

-- Oracle
#check @TruthOracle
#check @oracle_not_internalizable

#print "✅ Core exports verified"
