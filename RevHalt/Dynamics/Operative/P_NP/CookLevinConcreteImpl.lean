import RevHalt.Dynamics.Operative.P_NP.CookLevinMap
import RevHalt.Dynamics.Operative.P_NP.CookLevinConcrete
import RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets
import RevHalt.Dynamics.Operative.P_NP.CookLevinTableau
import RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness
import RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas
import RevHalt.Dynamics.Operative.P_NP.CookLevin
import Mathlib.Data.Nat.Basic

set_option maxHeartbeats 2000000

/-!
  RevHalt.Dynamics.Operative.P_NP.CookLevinConcreteImpl

  Concrete Cook-Levin implementation using the Tableau encoding.

  This file connects the generic `CookLevinEncodingWIP` interface
  to the concrete `genTableau` CNF generator.

  ## Status
  - encode: implemented via `genTableau` (uniqueness constraints only for now)
  - map: placeholder (sorry)
  - bounds: polynomial bounds proven (modulo genTableau sizing lemma)
  - encode_sat_iff: sorry (requires full tableau logic)
-/



namespace RevHalt.Dynamics.Operative.P_NP.CookLevinConcreteImpl

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.CookLevin
open RevHalt.Dynamics.Operative.P_NP.CookLevinConcrete
open RevHalt.Dynamics.Operative.P_NP.SATCanonical
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF
open RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets
open RevHalt.Dynamics.Operative.P_NP.CookLevinTableau

variable {PropT : Type}

abbrev SATP (B : SATBundle PropT) : RHProblem CNF.CNF := B.SATP

/-! ### §1. WIP Construction from SimBuilder -/

open RevHalt.Dynamics.Operative.P_NP.CookLevinMap
open RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness
open RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas

/--
Build a WIP template using the Tableau encoding with a Simulation Builder.
This abstracts away the Machine construction into `simBuilder`.
-/
def mkWIP_tableau
    (B : SATBundle PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    : CookLevinEncodingWIP B :=
{ encode := fun {ι} P V x => CookLevinCorrectness.encode (simBuilder P V) x

  map := fun {ι} P V =>
    BoolLRBundle.graphProblem BL
      (fun x => P.size x)
      (fun F => (SATP B).size F)
      (fun x => CookLevinCorrectness.encode (simBuilder P V) x)

  map_in_P := by
    intro ι P V
    exact BoolLRBundle.graphProblem_in_P BL
      (fun x => P.size x)
      (fun F => (SATP B).size F)
      (fun x => CookLevinCorrectness.encode (simBuilder P V) x)

  map_correct := by
    intro ι P V x y
    simpa using
      (BoolLRBundle.graphProblem_correct BL
        (fun x => P.size x)
        (fun F => (SATP B).size F)
        (fun x => CookLevinCorrectness.encode (simBuilder P V) x) x y)

  map_sizeBound := fun {ι} _P _V n => 2 * n + 1
  poly_map_sizeBound := by
    intro ι P V
    apply IsPoly.add
    apply IsPoly.mul
    apply IsPoly.const
    apply IsPoly.id
    apply IsPoly.const

  map_size_ok := by
    intro ι P V x y
    unfold BoolLRBundle.graphProblem
    dsimp
    -- size(x) + size(y) ≤ 2 * (size(x) + size(y)) + 1
    -- Proof strategy:
    -- 1. N ≤ 2*N (via two_mul and le_add_left)
    -- 2. 2*N ≤ 2*N + 1 (via le_add_right)
    apply Nat.le_trans (m := 2 * (P.size x + (SATP B).size y))
    · rw [two_mul]
      exact Nat.le_add_left _ _
    · exact Nat.le_add_right _ _

  out_sizeBound := fun {ι} P V n =>
    tableauFullSizeBoundFun (simBuilder P V).M (2 * (V.time n))

  poly_out_sizeBound := by
    intro ι P V
    -- isPoly composition (proof deferred, depends on Tableau bounds)
    sorry

  out_size_ok := by
    intro ι P V x
    have h := encode_size_poly (simBuilder P V) x
    simpa [CookLevinCorrectness.encode, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

  encode_sat_iff := by
    intro ι P V x
    let sim := simBuilder P V
    let F : CNF.CNF := CookLevinCorrectness.encode sim x

    -- (1) Solves SATP ↔ ∃wSAT bounded ∧ evalCNF wSAT F = true
    have hSolve :
        Solves (SATP B) F ↔
          ∃ w : Witness,
            witnessSize w ≤ B.wBound (cnfSize F) ∧
            CNF.evalCNF w F = true := by
      simpa [SATP, SATBundle.SATP] using (B.solves_sat_iff_bounded (F := F))

    -- (2) CNF.Satisfiable F ↔ bounded form, via maxVar hypothesis
    have hMax :
        maxVar F + 1 ≤ B.wBound (cnfSize F) := by
      exact B.wBound_ge_maxVar F

    have hSatBound :
        (∃ w : Witness, witnessSize w ≤ B.wBound (cnfSize F) ∧ CNF.evalCNF w F = true) ↔
          CNF.Satisfiable F := by
      simpa using (satisfiable_bounded_iff_satisfiable (wBound := B.wBound (cnfSize F)) (F := F) hMax).symm

    -- (3) CNF.Satisfiable (encode sim x) ↔ ∃wVerif bounded ∧ HaltsBy LR
    have hCL :
        CNF.Satisfiable F ↔
          (∃ w : Witness,
            witnessSize w ≤ V.wBound (P.size x) ∧
            HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w))
                   (V.time (P.size x))) := by
      simpa [F, CookLevinCorrectness.encode] using (CookLevinCorrectness.encode_sat_iff (sim := sim) (x := x))

    -- Assemblage
    exact hSolve.trans (hSatBound.trans hCL)
}

/-! ### §2. Final Connector: CookLevinKernel -/

/--
Canonical construction of the Cook-Levin Kernel.
Inputs:
- B: a SATBundle (target problem + logic bridges)
- simBuilder: a way to build TableauMachines for any Verifier
- BL: a BoolLRBundle for the syntactic check map
-/
def kernelOfSimBuilder
    (B : SATBundle PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    : CookLevinKernel (SATP B) :=
  kernel_of_wip B (mkWIP_tableau B simBuilder BL)

/--
NP-Hardness corollary.
IF we have a Simulator and a Bool Bundle, THEN SATP is NP-Hard.
-/
theorem NPHard_of_simBuilder
    (B : SATBundle PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    : NPHard_RH (SATP B) :=
  nphard_of_kernel (SATP B) (kernelOfSimBuilder B simBuilder BL)

/--
NP-Completeness corollary.
IF we have a Simulator and a Bool Bundle, THEN SATP is NP-Complete.
-/
theorem NPComplete_of_simBuilder
    (B : SATBundle PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    (hNP : NP_RH (SATP B)) -- Extra assumption needed for completeness
    : SAT_NPComplete_RH (SATP B) :=
  npcomplete_of_kernel (SATP B) hNP (kernelOfSimBuilder B simBuilder BL)

end RevHalt.Dynamics.Operative.P_NP.CookLevinConcreteImpl
