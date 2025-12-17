/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness

  Stage C: Verification bundle connecting tableau execution to HaltsBy LR.
  This provides the final semantic bridge for encode_sat_iff.
-/
import RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas
import RevHalt.Dynamics.Operative.P_NP.CookLevinSemantics
import RevHalt.Dynamics.Operative.P_NP.PNP
import RevHalt.Dynamics.Operative.P_NP.CookLevin
import RevHalt.Dynamics.Operative.P_NP.SAT

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness

open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF
open RevHalt.Dynamics.Operative.P_NP.CookLevinTableau
open RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas
open RevHalt.Dynamics.Operative.P_NP.CookLevinSemantics

/-! ## Verifier Tableau Simulation Bundle -/

/--
Specifies that a TableauMachine M simulates the verifier LR of a problem (P, V).

This is the **key Stage C abstraction**: it encapsulates the (non-combinatorial)
assumption that the tableau machine correctly simulates the LR-based verification.

Fields:
- Machine parameters: M, q0, head0, qAcc, sym0, sym1
- Encoding functions: witOff, tape0 (input-dependent)
- Core lemma: `run_iff_haltsBy` — the semantic bridge
-/
structure VerifierTableauSim {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) where
  /-- The tableau machine that simulates the verifier. -/
  M       : TableauMachine
  /-- Initial state. -/
  q0      : ℕ
  /-- Initial head position. -/
  head0   : ℕ
  /-- Accepting state. -/
  qAcc    : ℕ
  /-- Symbol for witness bit 0. -/
  sym0    : ℕ
  /-- Symbol for witness bit 1. -/
  sym1    : ℕ
  /-- Witness offset on tape (input-dependent). -/
  witOff  : ι → ℕ
  /-- Initial tape contents (input-dependent, without witness). -/
  tape0   : ι → (ℕ → ℕ)

  /-- Machine has enough states/symbols for the encoding. -/
  h_states : q0 < M.numStates
  h_qAcc   : qAcc < M.numStates
  h_sym0   : sym0 < M.numSymbols
  h_sym1   : sym1 < M.numSymbols

  /--
  **Core Stage C Lemma**: ValidRun ⟺ HaltsBy LR.

  This is the unique semantic bridge:
  - Left: existence of a valid tableau run (from SAT satisfiability via Stage A)
  - Right: existence of a witness that makes the verifier halt in time (LR semantics)
  -/
  run_iff_haltsBy :
    ∀ x : ι,
      (∃ R : TableauRun,
        ValidRun
          (V.time (P.size x)) (V.time (P.size x)) M
          q0 head0 qAcc (tape0 x)
          (V.wBound (P.size x)) (witOff x) sym0 sym1 R)
      ↔
      (∃ w : Witness,
        witnessSize w ≤ V.wBound (P.size x) ∧
        HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w))
               (V.time (P.size x)))

/-! ## Derived Theorems from VerifierTableauSim -/

variable {ι : Type} {P : RHProblem ι} {V : PolyVerifier P}
variable (sim : VerifierTableauSim P V)

/-- Combine Stage A + Stage C: CNF.Satisfiable ⟺ HaltsBy. -/
theorem satisfiable_iff_haltsBy (x : ι) :
    CNF.Satisfiable (genTableauAll
      (V.time (P.size x)) (V.time (P.size x)) sim.M
      sim.q0 sim.head0 sim.qAcc (sim.tape0 x)
      (V.wBound (P.size x)) (sim.witOff x) sim.sym0 sim.sym1)
    ↔
    (∃ w : Witness,
      witnessSize w ≤ V.wBound (P.size x) ∧
      HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w))
             (V.time (P.size x))) := by
  rw [tableau_satisfiable_iff_exists_run]
  exact sim.run_iff_haltsBy x

/-- The encode function for CookLevinKernel. -/
def encode (sim : VerifierTableauSim P V) (x : ι) : CNF.CNF :=
  genTableauAll
    (V.time (P.size x)) (V.time (P.size x)) sim.M
    sim.q0 sim.head0 sim.qAcc (sim.tape0 x)
    (V.wBound (P.size x)) (sim.witOff x) sim.sym0 sim.sym1

/-- Main Stage C result: encode produces a formula satisfiable iff verifier accepts. -/
theorem encode_sat_iff (x : ι) :
    CNF.Satisfiable (encode sim x)
    ↔
    (∃ w : Witness,
      witnessSize w ≤ V.wBound (P.size x) ∧
      HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w))
             (V.time (P.size x))) :=
  satisfiable_iff_haltsBy sim x

/-! ## Size Bounds for CookLevinKernel -/

/-- Size of encoded CNF is polynomial in input size. -/
theorem encode_size_poly (x : ι) :
    cnfSize (encode sim x) ≤ tableauFullSizeBoundFun sim.M (V.time (P.size x) * 2) := by
  sorry

/-- Max variable index is bounded polynomially. -/
theorem encode_maxVar_poly (x : ι) :
    maxVar (encode sim x) + 1 ≤ tableauFullSizeBoundFun sim.M (V.time (P.size x) * 2) := by
  sorry

/-! ## Construction of CookLevinKernel from VerifierTableauSim

Note: The actual `kernelOfSim` definition is in CookLevinConcreteImpl.lean
as it requires the full CookLevinKernel machinery. Here we provide the
core `encode_sat_iff` theorem which is the key input to that construction.

The chain is:
1. `Solves (SATP B) (encode sim x)`
2. ↔ `∃ wSAT, ... ∧ evalCNF wSAT (encode sim x) = true` (SATBundle.solves_sat_iff_bounded)
3. ↔ `CNF.Satisfiable (encode sim x)` (satisfiable_bounded_iff_satisfiable)
4. ↔ `∃ R, ValidRun ... R` (tableau_satisfiable_iff_exists_run from Stage A)
5. ↔ `∃ w, ... ∧ HaltsBy ...` (run_iff_haltsBy from VerifierTableauSim)
-/

end RevHalt.Dynamics.Operative.P_NP.CookLevinCorrectness
