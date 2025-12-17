/-
  RevHalt.Dynamics.Operative.P_NP.SAT

  Canonical SAT + Cook–Levin signature (internal RevHalt).
-/

import RevHalt.Dynamics.Operative.P_NP.PNP

namespace RevHalt.Dynamics.Operative.P_NP.SAT

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP

/-
  1) Pure CNF semantics on Witness = List Bool (no ctx involved).
-/
namespace CNF

abbrev Var := ℕ

structure Lit where
  v   : Var
  neg : Bool
  deriving DecidableEq

abbrev Clause := List Lit
abbrev CNF := List Clause

/-- decode variable value from witness bitstring; default = false if out of range -/
def evalVar (w : Witness) (v : Var) : Bool :=
  w.getD v false

def evalLit (w : Witness) (ℓ : Lit) : Bool :=
  let b := evalVar w ℓ.v
  if ℓ.neg then !b else b

def evalClause (w : Witness) (C : Clause) : Bool :=
  C.any (evalLit w)

def evalCNF (w : Witness) (F : CNF) : Bool :=
  F.all (evalClause w)

def SatWitness (F : CNF) (w : Witness) : Prop :=
  evalCNF w F = true

def Satisfiable (F : CNF) : Prop :=
  ∃ w : Witness, SatWitness F w

/-- size model (you can refine later; keep consistent with SATP.size) -/
def cnfSize (F : CNF) : ℕ := F.length

end CNF


/-
  2) "SATP is really SAT" = semantics lemmas tying Solves(SATP) to CNF.Satisfiable.
-/

/-- SATSemantics: Solves SATP ↔ ∃ w, evalCNF w F = true -/
structure SATSemantics (SATP : RHProblem CNF.CNF) : Prop where
  solves_iff_satisfiable : ∀ F : CNF.CNF, Solves SATP F ↔ CNF.Satisfiable F

/-- SATSound is an alias for SATSemantics (common terminology). -/
abbrev SATSound := SATSemantics

/-- Given a PolyVerifier for SATP, we get SAT ∈ NP_RH. -/
theorem SAT_in_NP_of_verifier
    (SATP : RHProblem CNF.CNF)
    (V : PolyVerifier SATP) :
    NP_RH SATP :=
  ⟨V, trivial⟩


/-
  3) Cook–Levin builder: uniform, explicit reduction constructor.
  (Returns PolyManyOneReduction, not just existence.)
-/
structure CookLevinBuilder (SATP : RHProblem CNF.CNF) : Type 1 :=
  (reduce :
    ∀ {ι : Type} (P : RHProblem ι),
      PolyVerifier P → PolyManyOneReduction P SATP)


/-
  4) NP-hardness / NP-completeness (internal, operative).
-/

/-- NP-hardness (operative): every NP_RH problem reduces to `SATP`. -/
def NPHard_RH (SATP : RHProblem CNF.CNF) : Prop :=
  ∀ {ι : Type} (P : RHProblem ι), NP_RH P → P ≤ₚ SATP

/-- A Cook–Levin builder yields NP-hardness. -/
theorem nphard_of_builder (SATP : RHProblem CNF.CNF) (B : CookLevinBuilder SATP) :
    NPHard_RH SATP := by
  intro ι P hNP
  rcases hNP with ⟨V, _⟩
  exact ⟨B.reduce P V, trivial⟩

/-- NP-completeness (operative): NP membership + NP-hardness. -/
def SAT_NPComplete_RH (SATP : RHProblem CNF.CNF) : Prop :=
  NP_RH SATP ∧ NPHard_RH SATP

theorem cookLevin_implies_SAT_NPComplete
    (SATP : RHProblem CNF.CNF)
    (hSAT_in_NP : NP_RH SATP)
    (CL : CookLevinBuilder SATP) :
    SAT_NPComplete_RH SATP :=
  ⟨hSAT_in_NP, nphard_of_builder SATP CL⟩

end RevHalt.Dynamics.Operative.P_NP.SAT
