/-
  RevHalt.Dynamics.Operative.SAT

  SAT (CNF) as a target problem for operative (internal) NP-completeness work.

  This file is intentionally "signature-first":
  - It provides a computable CNF syntax layer (CNF, eval under List Bool witnesses).
  - It provides builders/signatures to package SAT as an RHProblem (LR-coded) inside a chosen ctx.
  - No proofs of NP-completeness here; just the stable interfaces you will use in later files.
-/

import RevHalt.Dynamics.Operative.P_NP.PNP
import Mathlib.Data.List.Basic

namespace RevHalt.Dynamics.Operative.P_NP.SAT

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP

/-! ## §1. CNF Syntax (computable) -/

/-- Variables are naturals. -/
abbrev Var : Type := ℕ

/-- Literal = (variable, polarity). `neg = true` means ¬x_v. -/
structure Lit where
  v   : Var
  neg : Bool
  deriving DecidableEq

/-- Clause = disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- CNF = conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Coarse syntactic size (you can refine later). -/
def cnfSize (F : CNF) : ℕ := F.length

/-! ## §2. Witness semantics (computable) -/

/-- Interpretation of a `Witness := List Bool` as a partial assignment:
    variable `v` reads the `v`-th bit, defaulting to false if out of range. -/
def valOf (w : Witness) (v : Var) : Bool :=
  w.getD v false

def evalLit (w : Witness) (ℓ : Lit) : Bool :=
  let b := valOf w ℓ.v
  if ℓ.neg then (!b) else b

def evalClause (w : Witness) (C : Clause) : Bool :=
  C.any (fun ℓ => evalLit w ℓ)

def evalCNF (w : Witness) (F : CNF) : Bool :=
  F.all (fun C => evalClause w C)

/-- Boolean satisfiability of CNF under a witness assignment (computable). -/
def Sat (w : Witness) (F : CNF) : Prop :=
  evalCNF w F = true

/-! ## §3. LR-coded SAT as an RHProblem -/

/--
`SAT_RHProblem` packages SAT as an `RHProblem CNF` inside an arbitrary `VerifiableContext`.

You supply the encoding into `PropT`:
- `Γsat F : Finset PropT`  (finite context describing the instance)
- `φsat F : PropT`         (goal sentence: "F is satisfiable" in your encoding)
together with a polynomial bound on `|Γsat F|`.
-/
def SAT_RHProblem
    {Code PropT : Type}
    (ctx : VerifiableContext Code PropT)
    (Γsat : CNF → Finset PropT)
    (φsat : CNF → PropT)
    (Γ_bound : ℕ → ℕ)
    (poly_Γ_bound : IsPoly Γ_bound)
    (Γ_ok : ∀ F, (Γsat F).card ≤ Γ_bound (cnfSize F))
    : RHProblem CNF :=
{ Code := Code
  PropT := PropT
  ctx := ctx
  size := cnfSize
  Γ := Γsat
  φ := φsat
  Γ_bound := Γ_bound
  poly_Γ_bound := poly_Γ_bound
  Γ_ok := Γ_ok }

/-- Convenience: the internal proposition "SAT is in NP_RH" for a chosen encoding. -/
def SAT_in_NP
    {Code PropT : Type}
    (ctx : VerifiableContext Code PropT)
    (Γsat : CNF → Finset PropT)
    (φsat : CNF → PropT)
    (Γ_bound : ℕ → ℕ)
    (poly_Γ_bound : IsPoly Γ_bound)
    (Γ_ok : ∀ F, (Γsat F).card ≤ Γ_bound (cnfSize F))
    : Prop :=
  NP_RH (SAT_RHProblem ctx Γsat φsat Γ_bound poly_Γ_bound Γ_ok)

/-! ## §4. "Signature" for an NP verifier for SAT (locked Witness = List Bool) -/

/--
Minimal signature you will typically implement to prove `SAT_in_NP`:
it matches the fields needed to build a `PolyVerifier (SAT_RHProblem ...)`.
-/
structure SATVerifierSig {Code PropT : Type} (ctx : VerifiableContext Code PropT) where
  VΓ        : CNF → Witness → Finset PropT
  Vφ        : CNF → Witness → PropT
  time      : ℕ → ℕ
  wBound    : ℕ → ℕ
  ctx_bound : ℕ → ℕ
  poly_time      : IsPoly time
  poly_wBound    : IsPoly wBound
  poly_ctx_bound : IsPoly ctx_bound
  ctx_ok : ∀ F w, (VΓ F w).card ≤ ctx_bound (cnfSize F + witnessSize w)

/-! ## §5. Cook–Levin Internal Signature -/

/-
  The "Cook–Levin kernel" is the core of NP-completeness:
  a *uniform* construction that, given any NP verifier, builds a polytime
  many-one reduction to SAT.
-/

/--
Cook–Levin Builder (constructive form):
Given any problem `P` with a `PolyVerifier`, build a `PolyManyOneReduction P SATP`.
-/
def CookLevinBuilder (SATP : RHProblem CNF) : Type 1 :=
  ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → PolyManyOneReduction P SATP

/--
Cook–Levin Kernel (property form):
Every NP_RH problem reduces to SATP.
-/
def CookLevinKernel (SATP : RHProblem CNF) : Prop :=
  ∀ {ι : Type} (P : RHProblem ι), NP_RH P → (P ≤ₚ SATP)

/--
The link: a builder gives the kernel (by unpacking `NP_RH = ∃ verifier`).
-/
theorem cookLevinKernel_of_builder (SATP : RHProblem CNF) :
    CookLevinBuilder SATP → CookLevinKernel SATP := by
  intro build
  intro ι P hNP
  rcases hNP with ⟨V, _⟩
  refine ⟨build P V, trivial⟩

/--
SAT NP-completeness goal (internal):
SATP ∈ NP_RH and Cook–Levin kernel holds.
-/
def SAT_NPComplete_Goal (SATP : RHProblem CNF) : Prop :=
  NP_RH SATP ∧ CookLevinKernel SATP

end RevHalt.Dynamics.Operative.P_NP.SAT
