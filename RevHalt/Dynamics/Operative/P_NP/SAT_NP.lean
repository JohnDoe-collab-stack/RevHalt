/-
  RevHalt.Dynamics.Operative.SAT_NP

  Packaging: from an LR-encoding of SAT + an LR-verifier spec (locked Witness),
  build an NP_RH witness (PolyVerifier) for the resulting SAT_RHProblem.

  No completeness / NP-hardness here. Just the internal NP-membership interface.
-/

import RevHalt.Dynamics.Operative.P_NP.SAT
import RevHalt.Dynamics.Operative.P_NP.PNP

namespace RevHalt.Dynamics.Operative.P_NP.SAT_NP

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT

/-- Data needed to exhibit `SAT_RHProblem ... ∈ NP_RH`. -/
structure SATNPBundle {Code PropT : Type} (ctx : VerifiableContext Code PropT) where
  /- SAT problem encoding in PropT -/
  Γsat : CNF → Finset PropT
  φsat : CNF → PropT
  Γ_bound : ℕ → ℕ
  poly_Γ_bound : IsPoly Γ_bound
  Γ_ok : ∀ F, (Γsat F).card ≤ Γ_bound (cnfSize F)

  /- NP verifier encoding (locked Witness = List Bool) -/
  VΓ        : CNF → Witness → Finset PropT
  Vφ        : CNF → Witness → PropT
  time      : ℕ → ℕ
  wBound    : ℕ → ℕ
  ctx_bound : ℕ → ℕ
  poly_time      : IsPoly time
  poly_wBound    : IsPoly wBound
  poly_ctx_bound : IsPoly ctx_bound
  ctx_ok : ∀ F w, (VΓ F w).card ≤ ctx_bound (cnfSize F + witnessSize w)

  /- The key operative specification: problem-halting ↔ ∃ bounded witness with fast verifier-halting -/
  correct : ∀ F,
      Halts (ctx.LR (↑(Γsat F) : Set PropT) (φsat F)) ↔
        ∃ w : Witness,
          witnessSize w ≤ wBound (cnfSize F) ∧
          HaltsBy (ctx.LR (↑(VΓ F w) : Set PropT) (Vφ F w)) (time (cnfSize F))

/-- The SAT RHProblem induced by a bundle. -/
def SATP {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : RHProblem CNF :=
  SAT_RHProblem ctx B.Γsat B.φsat B.Γ_bound B.poly_Γ_bound B.Γ_ok

/-- The PolyVerifier induced by a bundle. -/
def satPolyVerifier {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : PolyVerifier (SATP B) where
  VΓ := B.VΓ
  Vφ := B.Vφ
  time := B.time
  wBound := B.wBound
  ctx_bound := B.ctx_bound
  poly_time := B.poly_time
  poly_wBound := B.poly_wBound
  poly_ctx_bound := B.poly_ctx_bound
  ctx_ok := B.ctx_ok
  correct := by
    intro F
    -- unfold Solves, RHProblem.tr, SATP, SAT_RHProblem; reduce to B.correct
    simp only [Solves, RHProblem.tr, SATP, SAT_RHProblem]
    exact B.correct F

/-- Final packaging: any bundle gives `NP_RH` for its SAT problem. -/
theorem SAT_in_NP_fromBundle {Code PropT : Type} {ctx : VerifiableContext Code PropT}
    (B : SATNPBundle ctx) : NP_RH (SATP B) :=
  ⟨satPolyVerifier B, trivial⟩

end RevHalt.Dynamics.Operative.P_NP.SAT_NP
