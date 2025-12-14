/-
  RevHalt.Instances.PA.Kit

  Standard Kit for PA instance.
  Same as PRModel: Proj := ∃ n, X n
-/
import RevHalt.Base

namespace RevHalt.Instances.PA

/-- Standard existence-based kit. -/
def PAKit : RHKit where
  Proj := fun X => ∃ n, X n

/-- PAKit detects monotone processes correctly. -/
theorem pa_kit_correct : DetectsMonotone PAKit := by
  intro X _hMono
  rfl

end RevHalt.Instances.PA
