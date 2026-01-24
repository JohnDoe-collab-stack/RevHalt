/-
  CollatzDynamicPA.lean

  But :
  - Mettre Collatz DANS le même fichier, et l’interfacer avec :
      * RevHalt.Trilemma.CofinalHornsSimple
      * RevHalt.Trilemma.CofinalHornsPA  (branche Strong : PairPA, cofinalités PA sur visites)
  - σ : Nat → Mode est défini de façon déterministe à partir d’un seed.

  Contrainte demandée :
  - pas de Classical
  - pas de noncomputable
  - éviter les “trucs” type mod6 : on utilise une classification par "branche else"
    (test x = 1, puis parité), donc 3 cas sans mod6.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

namespace Collatz

/-- Étape Collatz (sur Nat). -/
def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Itération Collatz : `iter k seed` = état après k pas. -/
def iter : Nat → Nat → Nat
  | 0,     seed => seed
  | k + 1, seed => iter k (step seed)

/-
  Encodage σ : Nat → Mode à partir de la trajectoire Collatz.

  Classification (sans mod6) :
    - si x = 1      => BC
    - sinon si x pair => AC
    - sinon           => AB
-/
def sigmaOf (seed : Nat) : Nat → Mode :=
  fun k =>
    let x := iter k seed
    if x = 1 then Mode.BC
    else if x % 2 = 0 then Mode.AC
    else Mode.AB

end Collatz


/-
  Instance "Collatz + DynamicPA Strong" :
  On fixe seed, donc on fixe σ := sigmaOf seed.
  Puis on applique directement le théorème Strong final déjà prouvé dans CofinalHornsPA.
-/
section CollatzDynamicPA

-- Contexte RevHalt / Trilemma
variable {Provable : Set PropT -> PropT -> Prop}
variable {K : RHKit}
variable {Machine : Code -> Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT -> Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

-- Hypothèses structurelles (celles utilisées partout dans le cadre)
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

-- Seed Collatz, et σ dérivé
variable (seed : Nat)
abbrev σ : Nat → Mode := Collatz.sigmaOf seed

-- Axiomes "PA internes" (comme ensemble de PropT)
variable (PAax : Set PropT)

/-
  Théorème : Collatz instancie σ, et sous :
    - cofinalité de σ sur chaque Mode,
    - witnesses forts PairPA pour chaque Mode,
  on obtient :
    - cofinalité des trois cornes,
    - cofinalité de PA sur les visites BC/AC/AB.
-/
theorem collatz_dynamicPA_Strong
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBC : SigmaCofinal (σ seed) .BC)
    (hAC : SigmaCofinal (σ seed) .AC)
    (hAB : SigmaCofinal (σ seed) .AB)
    (witBC :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC))
    (witAC :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC))
    (witAB :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB)) :
    let wBC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC witBC
    let wAC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC witAC
    let wAB :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .AB witBC witAC witAB) := by
  -- Application directe du théorème Strong final déjà prouvé
  exact dynamic_trilemma_with_PA_Strong_final
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn) (A0 := A0) (sigma := (σ seed)) (hIdem := hIdem) (hProvCn := hProvCn)
    PAax hMono hCnExt hBC hAC hAB witBC witAC witAB

end CollatzDynamicPA

end RevHalt.Trilemma
