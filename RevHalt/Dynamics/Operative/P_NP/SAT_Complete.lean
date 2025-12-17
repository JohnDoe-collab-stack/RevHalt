/-
  RevHalt.Dynamics.Operative.SAT_Complete

  Internal NP-completeness interface for SAT in the RevHalt operative universe.

  This file does NOT prove NP-hardness (that's the hard part).
  It only:
  - defines the internal notion `NPComplete_RH`,
  - packages "SAT ∈ NP_RH" (from SAT_NP.lean),
  - states the NP-hardness goal as a clean signature,
  - and provides the trivial constructor: (SAT ∈ NP) + (NP-hard) ⇒ (NP-complete).
-/

import RevHalt.Dynamics.Operative.P_NP.PNP
import RevHalt.Dynamics.Operative.P_NP.SAT
import RevHalt.Dynamics.Operative.P_NP.SAT_NP

namespace RevHalt.Dynamics.Operative.P_NP.SAT_Complete

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT_NP

/-! ### §1. Generic internal NP-completeness -/

/-- Internal NP-hardness (many-one reductions) for RH problems. -/
def NPHard_RH {κ : Type} (Q : RHProblem κ) : Prop :=
  ∀ {ι : Type} (P : RHProblem ι), NP_RH P → (P ≤ₚ Q)

/-- Internal NP-completeness: NP membership + NP-hardness (many-one). -/
def NPComplete_RH {κ : Type} (Q : RHProblem κ) : Prop :=
  NP_RH Q ∧ NPHard_RH Q

/-! ### §2. SAT-specific packaging -/

/-- The SAT problem induced by an `SATNPBundle` (same as in SAT_NP.lean). -/
abbrev SATProblem {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : RHProblem CNF :=
  SATP B

/-- SAT is in NP_RH as soon as you give an LR-encoding + LR-verifier bundle. -/
theorem SAT_in_NP {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : NP_RH (SATProblem B) :=
  SAT_in_NP_fromBundle B

/-- NP-hardness goal for SAT (internal, operative). -/
def SAT_is_NPHard {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : Prop :=
  NPHard_RH (SATProblem B)

/-- NP-completeness goal for SAT (internal, operative). -/
def SAT_is_NPComplete {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : Prop :=
  NPComplete_RH (SATProblem B)

/-- Constructor: if you provide NP-hardness, you get NP-completeness (since SAT ∈ NP). -/
theorem SAT_NPComplete_of_NPHard
    {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx)
    (hard : SAT_is_NPHard B) : SAT_is_NPComplete B := by
  refine ⟨SAT_in_NP B, ?_⟩
  exact hard

/-! ### §3. Optional: a "complete bundle" record -/

/-- A single object that carries SAT-in-NP data + the NP-hardness theorem. -/
structure SATCompleteBundle {Code PropT : Type} (ctx : VerifiableContext Code PropT) where
  base : SATNPBundle ctx
  hard : SAT_is_NPHard base

/-- Any complete bundle yields `SAT_is_NPComplete`. -/
theorem SAT_is_NPComplete_ofBundle
    {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (C : SATCompleteBundle ctx) : SAT_is_NPComplete C.base :=
  SAT_NPComplete_of_NPHard C.base C.hard

end RevHalt.Dynamics.Operative.P_NP.SAT_Complete
