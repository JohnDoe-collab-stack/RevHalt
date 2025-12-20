/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinConcrete

  Work-in-progress interface for Cook-Levin encoding.

  ## Architecture

  CookLevinEncodingWIP is the typed specification of what must be built
  to obtain a CookLevinKernel. Once filled, kernel_of_wip gives the kernel,
  which then yields NPHard_RH and NPComplete_RH via the existing lemmas.

  ## Next Steps

  1. Define encode (tableau → CNF)
  2. Define map (LR-coded map problem)
  3. Prove bounds (out_size_ok, map_size_ok)
  4. Prove encode_sat_iff (the core semantic lemma)
-/

import RevHalt.Dynamics.Operative.P_NP.CookLevin
import RevHalt.Dynamics.Operative.P_NP.SATCanonical

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinConcrete

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.CookLevin
open RevHalt.Dynamics.Operative.P_NP.SATCanonical
open RevHalt.Dynamics.Operative.P_NP.SAT

variable {Code PropT : Type} (B : SATBundle Code PropT)

abbrev SATP : RHProblem CNF.CNF := B.SATP

/--
"Work-in-progress" record: the typed specification of what must be built
to obtain a `CookLevinKernel (SATP B)`.

No field is "sorry": this is a typed checklist.
-/
structure CookLevinEncodingWIP : Type 1 where
  encode :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ι → CNF.CNF

  map :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → RHProblem (ι × CNF.CNF)

  map_in_P :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), P_RH (map P V)

  map_correct :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι) (y : CNF.CNF),
      Solves (map P V) (x, y) ↔ y = encode P V x

  map_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ℕ → ℕ
  poly_map_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), IsPoly (map_sizeBound P V)
  map_size_ok :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι) (y : CNF.CNF),
      (map P V).size (x, y) ≤ (map_sizeBound P V) (P.size x + (SATP B).size y)

  out_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ℕ → ℕ
  poly_out_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), IsPoly (out_sizeBound P V)
  out_size_ok :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι),
      (SATP B).size (encode P V x) ≤ (out_sizeBound P V) (P.size x)

  encode_sat_iff :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι),
      Solves (SATP B) (encode P V x) ↔
        ∃ w : Witness,
          witnessSize w ≤ V.wBound (P.size x) ∧
          HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w)) (V.time (P.size x))

/-- Once `W : CookLevinEncodingWIP B` is constructed, we get the kernel. -/
def kernel_of_wip (W : CookLevinEncodingWIP B) : CookLevinKernel (SATP B) :=
{ encode := @W.encode
  map := @W.map
  map_in_P := @W.map_in_P
  map_correct := @W.map_correct
  map_sizeBound := @W.map_sizeBound
  poly_map_sizeBound := @W.poly_map_sizeBound
  map_size_ok := @W.map_size_ok
  out_sizeBound := @W.out_sizeBound
  poly_out_sizeBound := @W.poly_out_sizeBound
  out_size_ok := @W.out_size_ok
  encode_sat_iff := @W.encode_sat_iff }

/-- From a WIP encoding, derive NPHard_RH. -/
theorem nphard_of_wip (W : CookLevinEncodingWIP B) : NPHard_RH (SATP B) :=
  nphard_of_kernel (SATP B) (kernel_of_wip B W)

/-- From a WIP encoding + SAT_in_NP, derive SAT_NPComplete_RH. -/
theorem npcomplete_of_wip (W : CookLevinEncodingWIP B) : SAT.SAT_NPComplete_RH (SATP B) :=
  npcomplete_of_kernel (SATP B) B.SAT_in_NP (kernel_of_wip B W)

end RevHalt.Dynamics.Operative.P_NP.CookLevinConcrete
