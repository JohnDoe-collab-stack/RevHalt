/-
  RevHalt.Core.API

  Core theorem index: #check statements for the main theorems.
  This file serves as a stable reference and anti-regression test.
-/

import RevHalt.Base.Trace
import RevHalt.Base.Kit
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Impossibility
import RevHalt.Theory.Complementarity
import RevHalt.Bridge.Context
import RevHalt.Dynamics.Core.Fuel
import RevHalt.Dynamics.Core.Fork
import RevHalt.Theory.ThreeBlocksArchitecture

namespace RevHalt.Core

/-!
## Closure Rigidity (T1)
-/

#check up              -- Trace → Trace (monotone closure)
#check Halts           -- Trace → Prop
#check up_mono         -- Monotone (up T)
#check exists_up_iff   -- Halts (up T) ↔ Halts T

#check DetectsMonotone -- Kit correctness on monotone traces
#check Rev0_K          -- K.Proj (up T)

#check T1_traces       -- Rev0_K K T ↔ Halts T
#check T1_uniqueness   -- Kit invariance

/-!
## Uniform Barrier (T2)
-/

#check T2_impossibility  -- No uniform internal halting predicate

/-!
## Local Certified Power (T3)
-/

#check true_but_unprovable_exists  -- Gap existence
#check GapWitness                   -- {p // Truth p ∧ ¬Provable p}
#check gapWitness_nonempty         -- GapWitness exists

-- Fuel (T2 as fuel for growth)
#check Dynamics.Core.Fuel.fuel_from_T2

-- Fork (two-sided complementarity)
#check Dynamics.Core.Fork.ofPivot
#check Dynamics.Core.Fork.exclusion

/-!
## Architecture (OracleMachine)
-/

#check aMachine                                -- Mechanical core
#check decidable_halts_of_decidable_eval       -- Eval decidable → Halts decidable
#check contradiction_if_internalize_external_decider  -- Internalize → T2 contradiction

end RevHalt.Core
