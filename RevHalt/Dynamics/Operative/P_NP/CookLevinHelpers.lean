/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinHelpers

  Derived lemmas and utilities for CookLevinKernel.
  - map_total / map_functional : automatic from map_correct
  - reduction_of_kernel : explicit PolyManyOneReduction builder
-/

import RevHalt.Dynamics.Operative.P_NP.CookLevin

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinHelpers

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.CookLevin

variable {SATP : RHProblem CNF.CNF} (K : CookLevinKernel SATP)

/-! ### Derived facts from `map_correct` -/

/-- Totality of the map: choose `y := encode x`. -/
theorem map_total
    {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) (x : ι) :
    ∃ y : CNF.CNF, Solves (K.map P V) (x, y) :=
  ⟨K.encode P V x, (K.map_correct P V x (K.encode P V x)).2 rfl⟩

/-- Functionality of the map: YES-instances force equality to `encode x`. -/
theorem map_functional
    {ι : Type} (P : RHProblem ι) (V : PolyVerifier P)
    (x : ι) (y y' : CNF.CNF)
    (hy : Solves (K.map P V) (x, y))
    (hy' : Solves (K.map P V) (x, y')) :
    y = y' := by
  have ey  : y  = K.encode P V x := (K.map_correct P V x y).1 hy
  have ey' : y' = K.encode P V x := (K.map_correct P V x y').1 hy'
  exact ey.trans ey'.symm

/-! ### Build the operative many-one reduction from the kernel -/

/-- The Cook–Levin reduction produced from a `CookLevinKernel`. -/
def reduction_of_kernel
    {ι : Type} (P : RHProblem ι) (V : PolyVerifier P) :
    PolyManyOneReduction P SATP where
  map := K.map P V
  map_in_P := K.map_in_P P V
  total := fun x => map_total K P V x
  functional := fun x y y' => map_functional K P V x y y'
  map_sizeBound := K.map_sizeBound P V
  poly_map_sizeBound := K.poly_map_sizeBound P V
  map_size_ok := K.map_size_ok P V
  sizeBound := K.out_sizeBound P V
  poly_sizeBound := K.poly_out_sizeBound P V
  size_ok := fun x y hxy => by
    have ey : y = K.encode P V x := (K.map_correct P V x y).1 hxy
    simp only [ey]
    exact K.out_size_ok P V x
  correct := fun x => by
    have hv := V.correct x
    have hk := K.encode_sat_iff P V x
    have hx : Solves P x ↔ Solves SATP (K.encode P V x) := hv.trans hk.symm
    constructor
    · intro hPx
      have hSat : Solves SATP (K.encode P V x) := hx.mp hPx
      exact ⟨K.encode P V x, (K.map_correct P V x (K.encode P V x)).2 rfl, hSat⟩
    · rintro ⟨y, hmap, hSat⟩
      have ey : y = K.encode P V x := (K.map_correct P V x y).1 hmap
      have hSat' : Solves SATP (K.encode P V x) := by simp only [← ey]; exact hSat
      exact hx.mpr hSat'

/-- Alternative builder using reduction_of_kernel. -/
def cookLevinBuilder' : SAT.CookLevinBuilder SATP where
  reduce := fun {_} P V => reduction_of_kernel K P V

end RevHalt.Dynamics.Operative.P_NP.CookLevinHelpers
