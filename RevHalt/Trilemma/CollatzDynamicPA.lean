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

/-- Alias pratique pour σ (évite les conflits d’abbrev). -/
abbrev sigmaCollatz (seed : Nat) : Nat → Mode := Collatz.sigmaOf seed

/- =====================================================================
   EXTINCTION DE AB (objectif) :
   Trilemme + Consistance (pont PA→RouteIIAt) + PA installé ⇒ AB s’éteint.
===================================================================== -/
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

-- Paramètre Collatz
variable (seed : Nat)

-- Axiomes PA internes
variable (PAax : Set PropT)

-- (3) Hypothèse positive : PA installé après un rang (sur le temps nat).
def PA_Eventually : Prop :=
  ∃ N, ∀ n, N ≤ n →
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax n

-- (2) Hypothèse de consistance structurante (pont) :
-- PA présent à l’instant t ⇒ RouteIIAt sur omegaΓ(chainState t).
def PA_implies_RouteIIAt : Prop :=
  ∀ t,
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t →
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

  -- Fait clé : k ≤ times ... k, via StrictStep + le_of_strictStep.
  let f : Nat → Nat :=
    fun m =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB m

  have hstep : StrictStep f := by
    intro m
    -- times_strictMono : times m < times (m+1)
    simpa [f] using
      (times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigmaCollatz seed) (hIdem := hIdem) (hProvCn := hProvCn)
        wBC wAC wAB m)

  have hk_le_t : k ≤ t := by
    have hk_le_fk : k ≤ f k := le_of_strictStep f hstep k
    simpa [t, f] using hk_le_fk

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

  -- Côté trilemme : si σ k = AB, strict_subseq_horns donne ¬RouteIIAt au même endroit (sur times ... k).
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
    -- hkAB force la branche AB du `match sigma k with ...`
    simpa [sigmaCollatz, t, hkAB] using hNotRoute_raw

  -- Contradiction : RouteIIAt ∧ ¬RouteIIAt.
  exact hNotRoute hRoute

/-
  Corollaire (ta formulation “quantité finie” au sens constructif) :
  Il existe une borne B telle que tout k avec σ k = AB satisfait k < B.
-/
theorem collatz_AB_indices_bounded_of_trilemma_and_consistency
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
    ∃ B, ∀ k, sigmaCollatz seed k = Mode.AB → k < B := by
  have hev : Collatz.EventuallyNotAB seed :=
    collatz_eventuallyNotAB_of_trilemma_and_consistency
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn)
      (hMono := hMono) (hCnExt := hCnExt) (seed := seed) (PAax := PAax)
      hPAev hBridge witBC witAC witAB

  rcases hev with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro k hkAB
  have : ¬ B ≤ k := by
    intro hBk
    exact (hB k hBk) hkAB
  exact Nat.lt_of_not_ge this

end ABExtinction

end RevHalt.Trilemma
