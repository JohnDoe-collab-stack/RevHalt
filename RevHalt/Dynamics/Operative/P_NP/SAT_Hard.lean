/-
  RevHalt.Dynamics.Operative.SAT_Hard

  SAT NP-hardness / NP-completeness layer (internal, operative).

  This file does NOT implement Cook–Levin.
  It cleanly isolates what you must ultimately provide:

  (Hardness Kernel)
    ∀ P ∈ NP_RH, P ≤ₚ SATP

  From that, you immediately get:
    SATP is NP-hard, and if also SATP ∈ NP_RH, then SATP is NP-complete.
-/

import RevHalt.Dynamics.Operative.P_NP.PNP
import RevHalt.Dynamics.Operative.P_NP.SAT
import RevHalt.Dynamics.Operative.P_NP.ReductionLibrary

namespace RevHalt.Dynamics.Operative.P_NP.SAT_Hard

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF
open RevHalt.Dynamics.Operative.P_NP.ReductionLibrary

/-! ### §1. NP-hardness kernel for SAT -/

/-- "Cook–Levin kernel" (as a single internal property): every NP problem reduces to SAT. -/
def SAT_HardKernel (SATP : RHProblem CNF.CNF) : Prop :=
  ∀ {ι : Type} (P : RHProblem ι), NP_RH P → (P ≤ₚ SATP)

/-- Kernel implies internal NP-hardness (by definition). -/
theorem SAT_NPHard_ofKernel (SATP : RHProblem CNF.CNF) :
    SAT_HardKernel SATP → RevHalt.Dynamics.Operative.P_NP.SAT.NPHard_RH SATP := by
  intro h
  exact h

/-- If you have (SAT ∈ NP) and the kernel, you get NP-completeness. -/
theorem SAT_NPComplete_ofKernel (SATP : RHProblem CNF.CNF) :
    NP_RH SATP → SAT_HardKernel SATP → NPComplete_RH SATP := by
  intro hNP hK
  exact ⟨hNP, hK⟩

/-! ### §2. A bundled form (useful for "one object carries the whole story") -/

structure SATCompleteKernel where
  SATP  : RHProblem CNF
  inNP  : NP_RH SATP
  hard  : SAT_HardKernel SATP

theorem SAT_is_NPComplete (K : SATCompleteKernel) : NPComplete_RH K.SATP :=
  ⟨K.inNP, K.hard⟩

end RevHalt.Dynamics.Operative.P_NP.SAT_Hard
