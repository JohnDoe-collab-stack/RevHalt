import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.Impossibility

namespace RevHalt

open Set

universe u

/--
  **ThreeBlocks Architecture (Abstract)**:
  A bundled structure connecting the three main components of RevHalt:
  1. **Calculation**: Machine/Code/Trace.
  2. **Certification**: Kit (Rev0, Stabilizes).
  3. **Theory**: Logic (ImpossibleSystem), Provability, Closure.

  This record provides the necessary hypotheses to trigger the dynamic theorems
  (Route II, Omega-Collapse) and instantiate the Two-Sided Dynamics.
-/
structure ThreeBlocks (PropT : Type) where
  -- Block 1: Theory
  S        : ImpossibleSystem PropT
  Provable : Set PropT → PropT → Prop
  Cn       : Set PropT → Set PropT

  -- Block 2: Calculation
  Code     : Type
  Machine  : Code → Trace
  K        : RHKit

  -- Block 3: Encoding
  encode_halt : Code → PropT

  -- Structural Hypotheses (Theory)
  hMono   : ProvRelMonotone Provable
  hCnExt  : CnExtensive Cn
  hCnMono : CnMonotone Cn
  hCnIdem : CnIdem Cn
  hProvCn : ProvClosedCn Provable Cn

  -- Structural Hypotheses (Kit)
  hK      : DetectsUpFixed K

  -- Bridge: Route II / T2 Hypotheses (Abstract)
  -- These allow us to derive frontier non-emptiness.
  -- (We assume standard Route II conditions here or derived lemmas)

/--
  **Canonical Not-Halt Encoding**:
  Defined via the system's negation: `encode_not_halt e := ¬ (encode_halt e)`.
-/
def encode_not_halt_canonical
    {PropT : Type}
    (TB : ThreeBlocks PropT) : TB.Code → PropT :=
  fun e => TB.S.Not (TB.encode_halt e)

/--
  **Bridging Lemma (One-Sided to Two-Sided)**:
  If the One-Sided frontier is non-empty (e.g., from Route II),
  then the Two-Sided frontier is non-empty.
-/
theorem S1Rel_pm_nonempty_of_S1Rel_nonempty
    {PropT : Type}
    (TB : ThreeBlocks PropT)
    (Γ : Set PropT)
    (hS1 : (S1Rel TB.Provable TB.K TB.Machine TB.encode_halt Γ).Nonempty) :
    (S1Rel_pm TB.Provable TB.K TB.Machine TB.encode_halt (encode_not_halt_canonical TB) Γ).Nonempty := by
  let S1 := S1Rel TB.Provable TB.K TB.Machine TB.encode_halt Γ
  let S1_pm := S1Rel_pm TB.Provable TB.K TB.Machine TB.encode_halt (encode_not_halt_canonical TB) Γ
  have hSub := S1Rel_subset_S1Rel_pm TB.Provable TB.K TB.Machine TB.encode_halt (encode_not_halt_canonical TB) Γ
  exact Set.Nonempty.mono hSub hS1

end RevHalt
