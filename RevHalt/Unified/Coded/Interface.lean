/-
  RevHalt.Unified.Coded.Interface

  Introduces **coded** versions of the Arithmetization interface.

  ## Motivation

  The original `Arithmetization` quantifies over `∀ G : Code → PropT`, which is
  impossible to instantiate for a real logic like PA (we can't compile a PredCode
  from an arbitrary Lean function).

  The solution: restrict to **coded families** of formulas, where `G` is itself
  computable/representable.

  ## Key Types

  - `FamilyCoding`: how to represent formula families via codes
  - `ArithmetizationCoded`: variant of Arithmetization for coded families
  - `HaltingEncoding`: same as E in the original pipeline
  - `SoundLogicEncodedCoded`: full package (L + A_coded + E)
-/
import RevHalt.Unified

namespace RevHalt_Unified.Coded
open RevHalt_Unified

/-- Coded families of formulas.
    Instead of `G : Code → PropT` (arbitrary Lean function), we use:
    - `GCode`: type of "codes" for formula families
    - `evalG`: evaluator giving the actual formula for each code + input -/
structure FamilyCoding (Code PropT : Type) where
  GCode : Type
  evalG : GCode → Code → PropT

/-- Arithmetization for coded families only.
    This is the key architectural change: we only require representability
    for families that are themselves computable/codable. -/
structure ArithmetizationCoded
    (M : RigorousModel) (PropT : Type) (L : SoundLogicDef PropT)
    (FC : FamilyCoding M.Code PropT) : Prop where
  /-- For each coded family g, there exists a predicate code pc such that
      M.PredDef pc e ↔ L.Provable (L.Not (FC.evalG g e)) -/
  repr_provable_not_coded :
    ∀ g : FC.GCode, ∃ pc : M.PredCode,
      ∀ e : M.Code, M.PredDef pc e ↔ L.Provable (L.Not (FC.evalG g e))

/-- Halting encoding (same as E in the original pipeline).
    Separated for clarity and reusability. -/
structure HaltingEncoding (M : RigorousModel) (PropT : Type) (L : SoundLogicDef PropT) where
  HaltEncode : M.Code → PropT
  encode_correct : ∀ e, RMHalts M e ↔ L.Truth (HaltEncode e)

/-- Full coded package: Logic (L) + Arithmetization_coded (A) + HaltEncoding (E).
    Parameterized by the family coding FC. -/
structure SoundLogicEncodedCoded (M : RigorousModel) (PropT : Type) where
  /-- How formula families are coded -/
  FC : FamilyCoding M.Code PropT
  /-- Pure logic (soundness, consistency, etc.) -/
  Logic : SoundLogicDef PropT
  /-- Coded arithmetization -/
  Arith : ArithmetizationCoded M PropT Logic FC
  /-- Halting encoding -/
  HaltE : HaltingEncoding M PropT Logic

end RevHalt_Unified.Coded
