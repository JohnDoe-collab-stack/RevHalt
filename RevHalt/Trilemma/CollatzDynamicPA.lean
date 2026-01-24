/-
  CollatzDynamicPA.lean

  Objectif (aligné sur ton objectif) :
  - Collatz DANS le même fichier.
  - σ := sigmaOf seed (déterministe).
  - Démontrer une extinction *positive* de AB (borne explicite) à partir de :
      (1) Trilemme (via strict_subseq_horns / HornAB_at_time)
      (2) Consistance structurante : Pont  (PA_at t → RouteIIAt sur omegaΓ(chainState t))
      (3) PA installé après un rang : ∃N, ∀n≥N, PA_at n
  - Aucune hypothèse "si ça atteint 1".
  - Pas de Classical, pas de noncomputable.
  - Pas de mod6 : classification par (x=1) puis parité.

  Idée formelle :
  - Si k est grand et σ k = AB, alors le trilemme donne ¬RouteIIAt au temps (times ... k).
  - Si PA est installé après N et si k≥N, alors (times ... k) ≥ k ≥ N,
    donc PA_at (times ... k), donc RouteIIAt par le pont.
  - Contradiction ⇒ σ k ≠ AB pour tout k≥N, donc AB est fini (au sens "plus jamais").
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
    - si x = 1        => BC
    - sinon si x pair => AC
    - sinon           => AB
-/
def sigmaOf (seed : Nat) : Nat → Mode :=
  fun k =>
    let x := iter k seed
    if x = 1 then Mode.BC
    else if x % 2 = 0 then Mode.AC
    else Mode.AB

/-- Extinction positive : à partir d’un rang N, on ne voit plus jamais AB. -/
def EventuallyNotAB (seed : Nat) : Prop :=
  ∃ N, ∀ k, N ≤ k → sigmaOf seed k ≠ Mode.AB

end Collatz

/-- Un alias pratique pour σ (évite les conflits de définitions). -/
abbrev sigmaCollatz (seed : Nat) : Nat → Mode := Collatz.sigmaOf seed

/- ============================================================================
   EXTINCTION DE AB (objectif) :
   Trilemme + Consistance (pont PA→RouteIIAt) + PA installé ⇒ AB s’éteint.
============================================================================ -/
section ABExtinction

-- Contexte RevHalt / Trilemma
variable {Provable : Set PropT → PropT → Prop}
variable {K : RHKit}
variable {Machine : Code → Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT → Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

-- Hypothèses structurelles
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

-- Hypothèses “trilemme” (CofinalHornsSimple)
variable (hMono : ProvRelMonotone Provable)
variable (hCnExt : CnExtensive Cn)

-- Paramètres Collatz
variable (seed : Nat)

-- Axiomes PA internes
variable (PAax : Set PropT)

-- (3) Hypothèse positive : PA installé après un rang, sur la chaîne (temps nat).
def PA_Eventually : Prop :=
  ∃ N, ∀ n, N ≤ n →
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax n

-- (2) Hypothèse de consistance structurante (pont) :
-- PA présent à l’instant t ⇒ RouteIIAt sur omegaΓ(chainState t).
def PA_implies_RouteIIAt : Prop :=
  ∀ t,
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t
    →
    RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
        (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t))

/-
  THÉORÈME (objectif) :
  Sous (1)(2)(3), AB s’éteint après un rang (donc nombre fini d’odd>1 sur la corne AB).
-/
theorem collatz_eventuallyNotAB_of_trilemma_and_consistency
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hPAev : PA_Eventually (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn)
      (PAax := PAax))
    (hBridge : PA_implies_RouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn)
      (PAax := PAax))
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)) :
    Collatz.EventuallyNotAB seed := by

  -- witnesses "simples" pour `times` et `strict_subseq_horns`
  let wBC :=
    toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC witBC
  let wAC :=
    toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC witAC
  let wAB :=
    toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB witAB

  rcases hPAev with ⟨N, hPA⟩
  refine ⟨N, ?_⟩
  intro k hkN
  intro hkAB

  -- t := times ... k
  let t :=
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB k

  -- Fait clé : k ≤ times ... k (donc N ≤ t si N ≤ k).
  have hk_le_t : k ≤ t := by
    -- strictStep : ∀k, times k < times (k+1)
    have hstep :
        ∀ m,
          times (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB m
            <
          times (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB (m + 1) :=
      fun m =>
        times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB m
    exact le_of_strictStep (f := fun m =>
        times (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB m) hstep k

  have hN_le_t : N ≤ t := Nat.le_trans hkN hk_le_t

  -- PA_at t puis RouteIIAt par le pont
  have hPA_t :
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t :=
    hPA t hN_le_t

  have hRoute :
      RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
          (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t)) :=
    hBridge t hPA_t

  -- Côté trilemme : si σ k = AB, alors ¬RouteIIAt au même endroit (sur t = times ... k).
  have hNotRoute_raw :=
    strict_subseq_horns (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigmaCollatz seed) hMono hCnExt hIdem hProvCn
      wBC wAC wAB k

  have hNotRoute :
      ¬ RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
          (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t)) := by
    -- spécialise la branche AB et aligne (times ... k) avec t
    have htmp := hNotRoute_raw
    -- sigmaCollatz seed k = AB est exactement hkAB
    -- (hkAB : Collatz.sigmaOf seed k = Mode.AB)
    -- et sigmaCollatz seed = Collatz.sigmaOf seed
    -- donc simp sait réduire le match.
    simpa [sigmaCollatz, t] using (by simpa [sigmaCollatz] using (by simpa [hkAB] using htmp))

  -- Contradiction
  exact hNotRoute hRoute

end ABExtinction


/- ============================================================================
   (Optionnel) Ton théorème Strong “cornes + PA sur visites” peut rester à part.
   Il ne sert pas à l’extinction AB (objectif ci-dessus).
============================================================================ -/
section CollatzDynamicPA

variable {Provable : Set PropT -> PropT -> Prop}
variable {K : RHKit}
variable {Machine : Code -> Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT → Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

variable (seed : Nat)
variable (PAax : Set PropT)

theorem collatz_dynamicPA_Strong
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBC : SigmaCofinal (sigmaCollatz seed) Mode.BC)
    (hAC : SigmaCofinal (sigmaCollatz seed) Mode.AC)
    (hAB : SigmaCofinal (sigmaCollatz seed) Mode.AB)
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)) :
    let wBC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC witBC
    let wAC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC witAC
    let wAB :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 (sigmaCollatz seed)
      hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 (sigmaCollatz seed)
      hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 (sigmaCollatz seed)
      hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (sigma := sigmaCollatz seed)
      hIdem hProvCn PAax Mode.BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (sigma := sigmaCollatz seed)
      hIdem hProvCn PAax Mode.AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (sigma := sigmaCollatz seed)
      hIdem hProvCn PAax Mode.AB witBC witAC witAB) := by
  exact dynamic_trilemma_with_PA_Strong_final
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn) (A0 := A0) (sigma := sigmaCollatz seed)
    (hIdem := hIdem) (hProvCn := hProvCn)
    PAax hMono hCnExt hBC hAC hAB witBC witAC witAB

end CollatzDynamicPA

end RevHalt.Trilemma
