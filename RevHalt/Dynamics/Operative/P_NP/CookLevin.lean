/-
  RevHalt.Dynamics.Operative.P_NP.CookLevin

  Cook–Levin (operative) as a *kernel interface*:

  If you provide a CookLevinKernel for a fixed SATP, you get:
  - a uniform CookLevinBuilder SATP
  - hence NPHard_RH SATP
  - and NPComplete_RH SATP once SATP ∈ NP_RH
-/

import RevHalt.Dynamics.Operative.P_NP.SAT

namespace RevHalt.Dynamics.Operative.P_NP.CookLevin

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT

/--
Cook–Levin kernel interface.

This is the *complete list of obligations* you must implement to obtain a
uniform builder `CookLevinBuilder SATP`.

Intuition:
- `encode P V x : CNF.CNF` is the Cook–Levin CNF encoding of the verifier run.
- `map P V : RHProblem (ι × CNF.CNF)` is the LR-coded operative map-problem
  whose YES-instances enforce `y = encode P V x` (no oracle function).
- `encode_sat_iff` is the core semantic lemma: SATP solves the encoding
  iff the verifier has a bounded-halting witness.
- size bounds are packaged in polynomial schemas (`IsPoly`).
- totality/functionality come from `map_correct` (uniqueness of the encoding).
-/
structure CookLevinKernel (SATP : RHProblem CNF.CNF) : Type 1 where
  /-- CNF encoding of the verifier computation for input `x`. -/
  encode :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ι → CNF.CNF

  /-- Operative map-problem witnessing y = encode(P,V,x) (LR-coded). -/
  map :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → RHProblem (ι × CNF.CNF)

  /-- The map-problem is in P_RH (operatively decidable in poly-time). -/
  map_in_P :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), P_RH (map P V)

  /-- Map correctness: YES-instances exactly enforce y = encode(P,V,x). -/
  map_correct :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι) (y : CNF.CNF),
      Solves (map P V) (x, y) ↔ y = encode P V x

  /-- Polynomial bound on map.size (prevents oracle via map sizing). -/
  map_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ℕ → ℕ

  /-- map_sizeBound is polynomial. -/
  poly_map_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), IsPoly (map_sizeBound P V)

  /-- map.size is bounded by map_sizeBound(P.size + SATP.size). -/
  map_size_ok :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι) (y : CNF.CNF),
      (map P V).size (x, y) ≤ (map_sizeBound P V) (P.size x + SATP.size y)

  /-- Polynomial bound on the output CNF size: SATP.size (encode ...) ≤ sizeBound(P.size x). -/
  out_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι), PolyVerifier P → ℕ → ℕ

  /-- out_sizeBound is polynomial. -/
  poly_out_sizeBound :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P), IsPoly (out_sizeBound P V)

  /-- Output size bound holds. -/
  out_size_ok :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι),
      SATP.size (encode P V x) ≤ (out_sizeBound P V) (P.size x)

  /--
  Core Cook–Levin semantic lemma:

  SATP solves the encoding iff there exists a bounded witness making the verifier halt.
  This is exactly what bridges NP-verification to SAT satisfiability internally.
  -/
  encode_sat_iff :
    ∀ {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι),
      Solves SATP (encode P V x) ↔
        ∃ w : Witness,
          witnessSize w ≤ V.wBound (P.size x) ∧
          HaltsBy (P.ctx.LR (↑(V.VΓ x w) : Set P.PropT) (V.Vφ x w)) (V.time (P.size x))

/-- From a kernel, build a uniform operative Cook–Levin builder. -/
def cookLevinBuilder_of_kernel {SATP : RHProblem CNF.CNF} (K : CookLevinKernel SATP) :
    CookLevinBuilder SATP where
  reduce := fun {ι} P V =>
  { map := K.map P V
    map_in_P := K.map_in_P P V
    total := fun x =>
      ⟨K.encode P V x, (K.map_correct P V x (K.encode P V x)).2 rfl⟩
    functional := fun x y y' hy hy' => by
      have ey  : y  = K.encode P V x := (K.map_correct P V x y).1 hy
      have ey' : y' = K.encode P V x := (K.map_correct P V x y').1 hy'
      simp [ey, ey']
    map_sizeBound := K.map_sizeBound P V
    poly_map_sizeBound := K.poly_map_sizeBound P V
    map_size_ok := K.map_size_ok P V
    sizeBound := K.out_sizeBound P V
    poly_sizeBound := K.poly_out_sizeBound P V
    size_ok := fun x y hxy => by
      have ey : y = K.encode P V x := (K.map_correct P V x y).1 hxy
      subst ey
      exact K.out_size_ok P V x
    correct := fun x => by
      constructor
      · intro hx
        have hv := (V.correct x).1 hx
        have hsat : Solves SATP (K.encode P V x) := (K.encode_sat_iff P V x).2 hv
        exact ⟨K.encode P V x, (K.map_correct P V x (K.encode P V x)).2 rfl, hsat⟩
      · rintro ⟨y, hmap, hsat⟩
        have ey : y = K.encode P V x := (K.map_correct P V x y).1 hmap
        subst ey
        have hv := (K.encode_sat_iff P V x).1 hsat
        exact (V.correct x).2 hv
  }

/-- Kernel ⇒ SAT is NP-hard (internal/operative). -/
theorem nphard_of_kernel (SATP : RHProblem CNF.CNF) (K : CookLevinKernel SATP) :
    NPHard_RH SATP :=
  nphard_of_builder SATP (cookLevinBuilder_of_kernel K)

/-- Kernel + SATP ∈ NP_RH ⇒ SATP is NP-complete (internal/operative). -/
theorem npcomplete_of_kernel (SATP : RHProblem CNF.CNF) (hNP : NP_RH SATP)
    (K : CookLevinKernel SATP) : SAT_NPComplete_RH SATP :=
  cookLevin_implies_SAT_NPComplete SATP hNP (cookLevinBuilder_of_kernel K)

end RevHalt.Dynamics.Operative.P_NP.CookLevin
