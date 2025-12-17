/-
  RevHalt.Dynamics.Operative.P_NP.SATCanonical

  Canonical SATP : RHProblem CNF.CNF + proof SAT ∈ NP_RH.

  ## Architecture

  SATBundle packages:
  - satProp : problem-level proposition "F is satisfiable"
  - satCheck : verifier-level proposition "w satisfies F"
  - time / wBound : polynomial bounds
  - sat_correct_bounded : problem ↔ ∃ bounded witness
  - satCheck_correct : verifier halts in bounded time ↔ evalCNF

  This eliminates the need for sorry placeholders.
-/

import RevHalt.Dynamics.Operative.P_NP.SAT

namespace RevHalt.Dynamics.Operative.P_NP.SATCanonical

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF

variable {PropT : Type}

/-- SATBundle "NP-ready" : provides all bounded bridges for NP_RH. -/
structure SATBundle (PropT : Type) where
  ctx : VerifiableContext CNF.CNF PropT

  /-- Proposition "F is satisfiable" (problem level). -/
  satProp : CNF.CNF → PropT

  /-- Proposition "w satisfies F" (verifier level). -/
  satCheck : CNF.CNF → Witness → PropT

  /-- NP bounds (depend only on cnfSize). -/
  time   : ℕ → ℕ
  wBound : ℕ → ℕ
  poly_time   : IsPoly time
  poly_wBound : IsPoly wBound

  /-- Problem bridge: halting LR of satProp ↔ ∃ bounded witness that satisfies. -/
  sat_correct_bounded :
    ∀ F,
      Halts (ctx.LR ∅ (satProp F)) ↔
        ∃ w : Witness,
          witnessSize w ≤ wBound (cnfSize F) ∧
          evalCNF w F = true

  /-- Verification bridge: verify w in bounded time. -/
  satCheck_correct :
    ∀ F w,
      HaltsBy (ctx.LR ∅ (satCheck F w)) (time (cnfSize F)) ↔
        evalCNF w F = true

namespace SATBundle
variable (B : SATBundle PropT)

/-- Canonical SATP (problem). -/
def SATP : RHProblem CNF.CNF where
  Code := CNF.CNF
  PropT := PropT
  ctx := B.ctx
  size := cnfSize
  Γ := fun _ => ∅
  φ := B.satProp
  Γ_bound := fun _ => 0
  poly_Γ_bound := IsPoly.const 0
  Γ_ok := fun _ => by simp

/-- Bounded form directly usable by NP_RH. -/
theorem solves_sat_iff_bounded (F : CNF.CNF) :
    Solves (SATP B) F ↔
      ∃ w : Witness,
        witnessSize w ≤ B.wBound (cnfSize F) ∧
        evalCNF w F = true := by
  unfold Solves RHProblem.tr SATP
  simp only [Finset.coe_empty]
  exact B.sat_correct_bounded F

/-- NP verifier for SATP. -/
def satVerifier : PolyVerifier (SATP B) where
  VΓ := fun _ _ => ∅
  Vφ := fun F w => B.satCheck F w
  time := B.time
  wBound := B.wBound
  ctx_bound := fun _ => 0
  poly_time := B.poly_time
  poly_wBound := B.poly_wBound
  poly_ctx_bound := IsPoly.const 0
  ctx_ok := fun _ _ => by simp
  correct := fun F => by
    constructor
    · intro hSolve
      -- Solves -> ∃w bounded ∧ eval=true (bundle)
      rcases (B.solves_sat_iff_bounded F).1 hSolve with ⟨w, hwB, hwSat⟩
      refine ⟨w, hwB, ?_⟩
      -- eval=true -> HaltsBy (bundle)
      have : HaltsBy (B.ctx.LR ∅ (B.satCheck F w)) (B.time (cnfSize F)) := by
        exact (B.satCheck_correct F w).2 hwSat
      simpa [HaltsBy] using this
    · rintro ⟨w, hwB, hBy⟩
      -- HaltsBy -> eval=true (bundle), then -> Solves (bundle)
      -- hBy : HaltsBy ... (B.time (B.SATP.size F)) = HaltsBy ... (B.time (cnfSize F))
      simp only [SATP, Finset.coe_empty] at hBy
      have hwSat : evalCNF w F = true := (B.satCheck_correct F w).1 hBy
      exact (B.solves_sat_iff_bounded F).2 ⟨w, hwB, hwSat⟩

/-- SAT ∈ NP_RH -/
theorem SAT_in_NP : NP_RH (SATP B) :=
  ⟨satVerifier B, trivial⟩

end SATBundle

/-!
## Section 2: SATP is the target for Cook-Levin

With SATP defined and SAT ∈ NP_RH established, SATP can serve as
the target problem for the CookLevinKernel.
-/

/-- SATP is a valid target for NP-completeness. -/
theorem SATP_valid (B : SATBundle PropT) : NP_RH (B.SATP) := B.SAT_in_NP

end RevHalt.Dynamics.Operative.P_NP.SATCanonical
