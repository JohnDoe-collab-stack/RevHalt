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

variable {Code PropT : Type}

abbrev SATP (B : SATBundle Code PropT) : RHProblem CNF.CNF := B.SATP

/-! ### §1. WIP Construction from SimBuilder -/

open RevHalt.Dynamics.Operative.P_NP.CookLevinMap
open RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness
open RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas

/-
  Local helpers for the schema:
  IsPoly f := ∃ c k, ∀ n, f n ≤ c * (n+1)^k + c
-/

private theorem IsPoly.mul_const_left (a : ℕ) {f : ℕ → ℕ} (hf : IsPoly f) :
    IsPoly (fun n => a * f n) := by
  rcases hf with ⟨c, k, hc⟩
  refine ⟨a * c, k, ?_⟩
  intro n
  have h := Nat.mul_le_mul_left a (hc n)
  -- a * (c*(n+1)^k + c) = (a*c)*(n+1)^k + (a*c)
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Composition lemma for the coarse IsPoly schema. -/
private theorem IsPoly.comp {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun n => f (g n)) := by
  rcases hf with ⟨cf, kf, hF⟩
  rcases hg with ⟨cg, kg, hG⟩

  -- A big constant for the substitution bound
  let A : ℕ := 2 * (cg + 2)
  let c : ℕ := cf * (A ^ kf) + cf
  let k : ℕ := kg * kf

  refine ⟨c, k, ?_⟩
  intro n
  have hF' := hF (g n)  -- f (g n) ≤ cf * (g n + 1)^kf + cf

  -- Bound: g n + 1 ≤ A * (n+1)^kg
  have hG0 : g n ≤ cg * (n + 1) ^ kg + cg := hG n
  have hG1 : g n + 1 ≤ cg * (n + 1) ^ kg + (cg + 1) := by
    have := Nat.add_le_add_right hG0 1
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

  have hPow1 : 1 ≤ (n + 1) ^ kg := by
    have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    exact Nat.one_le_pow _ _ hn

  have hMul_ge : cg + 1 ≤ (cg + 1) * (n + 1) ^ kg := by
    -- (cg+1)*1 ≤ (cg+1)*(n+1)^kg
    simpa [Nat.mul_one] using Nat.mul_le_mul_left (cg + 1) hPow1

  have hG2 :
      cg * (n + 1) ^ kg + (cg + 1)
        ≤ cg * (n + 1) ^ kg + (cg + 1) * (n + 1) ^ kg := by
    exact Nat.add_le_add_left hMul_ge _

  have hG3 :
      g n + 1
        ≤ cg * (n + 1) ^ kg + (cg + 1) * (n + 1) ^ kg := by
    exact Nat.le_trans hG1 hG2

  have hG4 :
      cg * (n + 1) ^ kg + (cg + 1) * (n + 1) ^ kg
        = (cg + (cg + 1)) * (n + 1) ^ kg := by
    -- (a*b) + (c*b) = (a+c)*b
    -- Nat.add_mul gives (a+c)*b = a*b + c*b
    simp [Nat.add_mul]

  have hcoef : cg + (cg + 1) ≤ A := by
    -- cg + (cg+1) = 2*cg + 1 ≤ 2*cg + 4 = 2*(cg+2)
    have h1 : cg + (cg + 1) = 2 * cg + 1 := by
      simp [two_mul, Nat.add_assoc]
    have h2 : 2 * cg + 1 ≤ 2 * cg + 4 := by
      exact Nat.add_le_add_left (show 1 ≤ 4 by decide) (2 * cg)
    have h3 : 2 * cg + 4 = A := by
      simp [A, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact h1 ▸ h3 ▸ h2

  have hG5 : g n + 1 ≤ A * (n + 1) ^ kg := by
    have h1 : g n + 1 ≤ (cg + (cg + 1)) * (n + 1) ^ kg := by
      simpa [hG4] using hG3
    have h2 : (cg + (cg + 1)) * (n + 1) ^ kg ≤ A * (n + 1) ^ kg :=
      Nat.mul_le_mul_right _ hcoef
    exact Nat.le_trans h1 h2

  -- Raise to kf: (g n + 1)^kf ≤ (A*(n+1)^kg)^kf
  have hPow :
      (g n + 1) ^ kf ≤ (A * (n + 1) ^ kg) ^ kf := by
    exact Nat.pow_le_pow_left hG5 _

  -- Rewrite (A * p)^kf = A^kf * p^kf = A^kf * (n+1)^(kg*kf)
  have hPow' :
      (A * (n + 1) ^ kg) ^ kf = (A ^ kf) * (n + 1) ^ (kg * kf) := by
    -- uses: (a*b)^k = a^k*b^k and (x^kg)^kf = x^(kg*kf)
    rw [Nat.mul_pow, ← Nat.pow_mul]

  have hSub :
      (g n + 1) ^ kf ≤ (A ^ kf) * (n + 1) ^ (kg * kf) := by
    simpa [hPow'] using hPow

  -- Plug back into f bound
  have hMain :
      f (g n) ≤ (cf * (A ^ kf)) * (n + 1) ^ (kg * kf) + cf := by
    -- from hF': f(g n) ≤ cf*(g n+1)^kf + cf
    refine Nat.le_trans hF' ?_
    have := Nat.add_le_add_right (Nat.mul_le_mul_left cf hSub) cf
    -- cf * ((A^kf) * X) = (cf*(A^kf)) * X
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

  -- Fit into c*(n+1)^k + c with c = cf*A^kf + cf
  have h1 :
      (cf * (A ^ kf)) * (n + 1) ^ (kg * kf)
        ≤ (cf * (A ^ kf) + cf) * (n + 1) ^ (kg * kf) := by
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

  have h2 : cf ≤ cf * (A ^ kf) + cf := by
    exact Nat.le_add_left _ _

  have := Nat.add_le_add h1 h2
  -- final rewrite to match chosen constants
  simpa [c, k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.le_trans hMain this

/--
Build a WIP template using the Tableau encoding with a Simulation Builder.
This abstracts away the Machine construction into `simBuilder`.
-/
def mkWIP_tableau
    (B : SATBundle Code PropT)
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
    have hF : IsPoly (tableauFullSizeBoundFun (simBuilder P V).M) :=
      poly_tableauFullSizeBoundFor (simBuilder P V).M
    have hG : IsPoly (fun n => 2 * V.time n) :=
      IsPoly.mul_const_left 2 V.poly_time
    exact IsPoly.comp hF hG

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
    (B : SATBundle Code PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    : CookLevinKernel (SATP B) :=
  kernel_of_wip B (mkWIP_tableau B simBuilder BL)

/--
NP-Hardness corollary.
IF we have a Simulator and a Bool Bundle, THEN SATP is NP-Hard.
-/
theorem NPHard_of_simBuilder
    (B : SATBundle Code PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    : NPHard_RH (SATP B) :=
  nphard_of_kernel (SATP B) (kernelOfSimBuilder B simBuilder BL)

/--
NP-Completeness corollary.
IF we have a Simulator and a Bool Bundle, THEN SATP is NP-Complete.
-/
theorem NPComplete_of_simBuilder
    (B : SATBundle Code PropT)
    (simBuilder : ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), VerifierTableauSim P V)
    (BL : BoolLRBundle)
    (hNP : NP_RH (SATP B)) -- Extra assumption needed for completeness
    : SAT_NPComplete_RH (SATP B) :=
  npcomplete_of_kernel (SATP B) hNP (kernelOfSimBuilder B simBuilder BL)

end RevHalt.Dynamics.Operative.P_NP.CookLevinConcreteImpl
