-- RevHalt/Demo/SimpDemo.lean
-- Contract tests for simp lemmas

import RevHalt.Bridge
import RevHalt.Demo.DemoC

/-!
# Simp Demo: Contract Tests

This file tests that simp lemmas correctly reduce context projections.
If these tests fail, the simp policy may need adjustment.
-/

namespace RevHalt_Demo_Simp
open RevHalt

-- Use the robust model from DemoC
open RevHalt_Demo_C

abbrev M := RevHalt_Demo_C.ToyModel
abbrev PropT := RevHalt_Demo_C.ToyPropT
abbrev K := RevHalt_Demo_C.ToyKit
abbrev hK := RevHalt_Demo_C.toy_kit_correct
abbrev L := RevHalt_Demo_C.ToyLogic

def ctx := EnrichedContext_from_Encoded M K hK L

-- Contract 1: RealHalts reduces to Halts (via RealHalts_encoded_simp)
example (e : M.Code) : Rev0_K K (rmCompile M e) ↔ Halts (rmCompile M e) := by
  simp [ctx, RealHalts_encoded_simp M K hK]

-- Contract 2: H reduces correctly
example (e : M.Code) : ctx.H e = L.HaltEncode e := by
  rfl

-- Contract 3: Provable reduces correctly
example (p : PropT) : ctx.Provable p ↔ L.Logic.Provable p := by
  rfl

-- Contract 4: Truth reduces correctly
example (p : PropT) : ctx.Truth p ↔ L.Logic.Truth p := by
  rfl

-- Contract 5: Not reduces correctly
example (p : PropT) : ctx.Not p = L.Logic.Not p := by
  rfl

-- Contract 6: FalseT reduces correctly
example : ctx.FalseT = L.Logic.FalseP := by
  rfl

-- Contract 7: Simp lemmas from Bridge work as expected
example (p : PropT) : (EnrichedContext_from_Encoded M K hK L).Provable p ↔ L.Logic.Provable p := by
  simp

example (p : PropT) : (EnrichedContext_from_Encoded M K hK L).Truth p ↔ L.Logic.Truth p := by
  simp

end RevHalt_Demo_Simp
