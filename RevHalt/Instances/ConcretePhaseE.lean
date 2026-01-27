import RevHalt.Instances.ConcreteBridgeMin
import RevHalt.Trilemma.GenericExtinction

namespace RevHalt.Instances

open RevHalt.Trilemma
open RevHalt.Trilemma.Generic

theorem eventuallyNotAB_of_concrete
    (D : ConcreteBridgeAssumptionsD)
    (sigma : Nat → Mode) :
    EventuallyNotAB sigma := by
  simpa using
    (eventuallyNotAB_of_instance (sigma := sigma) (I := ConcreteInstance_of_D D))

end RevHalt.Instances
