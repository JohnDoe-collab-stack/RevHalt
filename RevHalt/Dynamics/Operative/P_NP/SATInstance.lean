/-
  RevHalt.Dynamics.Operative.P_NP.SATInstance

  This file constructs a concrete `SATBundle` given a `TuringGodelContext`
  and the existence of encoded SAT solver/verifier programs.
  This formally establishes "SAT ∈ NP_RH" for any sufficiently expressive context.
-/
import RevHalt.Dynamics.Operative.P_NP.SATCanonical
import RevHalt.Dynamics.Operative.P_NP.SAT_RH
import RevHalt.Bridge.Context

namespace RevHalt.Dynamics.Operative.P_NP.SATInstance

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF
open RevHalt.Dynamics.Operative.P_NP.SATCanonical

variable {Code PropT : Type}
variable (ctx : VerifiableContext CNF.CNF PropT)

/--
Assumption 1: Existence of a SAT Solver program `solver F` in `Code`.
Its halting corresponds exactly to `F` being satisfiable.
-/
variable (solver : CNF.CNF → Code)

/--
Assumption 2: Existence of a Witness Verifier program `verifier F w` in `Code`.
Its halting corresponds exactly to `w` satisfying `F`.
Also requires polynomial time efficiency in relation to `maxVar F`.
-/
variable (verifier : CNF.CNF → PNP.Witness → Code)
variable (time : ℕ → ℕ)
variable (wBound : ℕ → ℕ)
variable (poly_time : IsPoly time)
variable (poly_wBound : IsPoly wBound)

-- Verification correctness: Halts in limited steps iff valid witness.
-- We state this directly on the bridged proposition to match SATBundle requirements.
variable (h_verifier : ∀ F w,
  ctx.HaltsBy (ctx.LR ∅ (ctx.H (verifier F w))) (time (cnfSize F)) ↔
  CNF.evalCNF w F = true)

-- Bounds consistency
variable (wBound_ge_maxVar : ∀ F, CookLevinLemmas.maxVar F + 1 ≤ wBound (cnfSize F))

-- Consistency between Solver and Verifier via Bounds.
-- The solver halts iff there exists a bounded witness that separates the verifier.
variable (h_bridge : ∀ F,
  ctx.RealHalts (solver F) ↔
    ∃ w : PNP.Witness, PNP.witnessSize w ≤ wBound (cnfSize F) ∧ CNF.evalCNF w F = true)

/--
Construct a SATBundle from the assumptions.
-/
def makeSATBundle : SATBundle PropT :=
  { ctx := ctx
    satProp := fun F => ctx.H (solver F)
    satCheck := fun F w => ctx.H (verifier F w)
    time := time
    wBound := wBound
    poly_time := poly_time
    poly_wBound := poly_wBound
    wBound_ge_maxVar := wBound_ge_maxVar
    sat_correct_bounded := by
      intro F
      -- ctx.LR ∅ (ctx.H p) <-> RealHalts p
      rw [ctx.h_bridge]
      -- RealHalts (solver F) <-> Exists bounded witness ...
      exact h_bridge F
    satCheck_correct := by
      intro F w
      exact h_verifier F w
  }

/--
Theorem: SAT is in NP_RH for this context.
-/
theorem SAT_in_NP_Instance : NP_RH ctx (fun F => ctx.H (solver F)) :=
  let bundle := makeSATBundle ctx solver verifier time wBound poly_time poly_wBound h_verifier wBound_ge_maxVar h_bridge
  SAT_in_NP bundle

end RevHalt.Dynamics.Operative.P_NP.SATInstance
