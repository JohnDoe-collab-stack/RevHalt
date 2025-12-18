import RevHalt.Dynamics.Instances.CollatzTrace
import RevHalt.Dynamics.Instances.TraceIndependence

namespace RevHalt.Dynamics.Instances.CollatzIndependence

open RevHalt
open RevHalt.Dynamics.Instances.CollatzTrace
open RevHalt.Dynamics.Instances.TraceIndependence

variable {Code PropT : Type}
variable (ctx : TuringGodelContext' Code PropT)

/-- Collatz = instance of generic pattern, Index = ℕ, trace = collatzTrace'. -/
abbrev CollatzCompiler := TraceCompiler (ctx := ctx)

-- You provide a value `comp : CollatzCompiler ctx` with
--   Index := ℕ
--   trace := collatzTrace'
--   code := collatzCode
--   code_inj := ...
--   halts_agree := ...
--
-- And you take f := id for "n kept".
-- Then apply `gate_unbounded_width`.

end RevHalt.Dynamics.Instances.CollatzIndependence
