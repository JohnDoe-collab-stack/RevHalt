/-
  RevHalt.Instances.PA.Main

  Entry point for the PA instance.

  ## Status

  This is a **skeleton** that outlines the structure.
  The actual proofs require:
  1. A real PA formalization (e.g., lean4-logic2)
  2. Gödel numbering of formulas
  3. Formalization of PA's proof checker as PR/RE

  ## Architecture

  Uses the **coded** pipeline (Unified/Coded/*) because:
  - Original Arithmetization requires `∀ G : Code → PropT` (impossible for PA)
  - Coded version requires `∀ g : GCode` (computable formula families only)

  ## Roadmap

  1. ✅ Interface.lean - FamilyCoding, ArithmetizationCoded
  2. ✅ Context.lean - TuringGodelContextCoded
  3. ✅ Master.lean - Coded master theorem
  4. ⬜ Logic.lean - Replace placeholders with real PA
  5. ⬜ Encoding.lean - Σ₁ halting formula + encode_correct
  6. ⬜ Arithmetization.lean - PR proof checker + repr_provable_not_coded
  7. ⬜ Main.lean - Final instantiation
-/
import RevHalt.Instances.PA.Kit
-- import RevHalt.Instances.PA.Logic  -- Has sorry/axiom - don't import yet
-- import RevHalt.Instances.PA.Encoding
-- import RevHalt.Instances.PA.Arithmetization
-- import RevHalt.Unified.Coded.Master

namespace RevHalt.Instances.PA
open RevHalt_Unified
-- open RevHalt_Unified.Coded

/-!
## Final Instantiation (Skeleton)

Once all components are complete, the final theorem will look like:

```lean
def PALogicEncodedCoded : SoundLogicEncodedCoded PAModel PASentence where
  FC := PAFamilyCoding
  Logic := PALogicDef
  Arith := ⟨pa_repr_provable_not_coded PAModel⟩
  HaltE := PAHaltingEncoding

theorem PA_Master_Theorem :
    let ctx := EnrichedContextCoded_from_RM PAModel PAKit pa_kit_correct PALogicEncodedCoded
    (∀ e, ctx.RealHalts e ↔ ctx.Truth (ctx.H e)) ∧
    (∃ e, ctx.RealHalts e ↔ ctx.Provable (ctx.Not (ctx.H e))) :=
  RevHalt_Master_Complete_Coded PAModel PAKit pa_kit_correct PALogicEncodedCoded
    halt_code hHalt_code
```
-/

#check PAKit
#check pa_kit_correct

end RevHalt.Instances.PA
