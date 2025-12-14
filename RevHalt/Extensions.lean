/-!
# RevHalt.Extensions

Entry point for Extension modules (OmegaChaitin, RefSystem).

These extensions currently use the legacy `RevHalt_Unified` namespace
for backward compatibility. They can be imported alongside the new
modular structure.
-/

-- Legacy imports that work with old Unified structure
-- (Extensions not yet migrated to new structure)
import RevHalt.Extensions.RefSystem
import RevHalt.Extensions.OmegaChaitin
