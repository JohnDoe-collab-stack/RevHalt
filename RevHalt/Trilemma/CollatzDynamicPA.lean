/-
  CollatzDynamicPA.lean

  Objectif (aligné sur ton objectif) :
  - Collatz DANS le même fichier.
  - σ := sigmaOf seed (déterministe).
  - Démontrer une extinction *positive* de AB (borne explicite) à partir de :
      (1) Trilemme (via strict_subseq_horns / HornAB_at_time)
      (2) Consistance structurante : Pont  (PA_at t → RouteIIAt sur omegaΓ(chainState t))
      (3) (SUPPRIMÉ) PA installé après un rang -> DÉRIVÉ de l'existence d'un witness PA.
  - Aucune hypothèse "si ça atteint 1".
  - Pas de Classical, pas de noncomputable.
  - Pas de mod6 : classification par (x=1) puis parité.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics

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

-- (2) Pont : PA_at t ⇒ RouteIIAt(omegaΓ(chainState t))
def PA_implies_RouteIIAt : Prop :=
  ∀ t,
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t →
    RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
        (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t))

/--
  Lemme local de monotonie pour chainState.
  Dérivé de `chainState_step_hom` (TheoryDynamics.lean) par induction.
-/
lemma chainState_mono
    (hCnExt : CnExtensive Cn)
    {t u : Nat} (htu : t ≤ u) :
    (chainState (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
       (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t).Γ ⊆
    (chainState (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
       (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) u).Γ := by
  induction htu with
  | refl => exact Set.Subset.refl _
  | step h ih =>
      apply Set.Subset.trans ih
      -- Robust call: expliciting structure arguments to avoid unification issues
      apply chainState_step_hom (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn)
        hIdem hProvCn hCnExt A0

/-- Monotonie de `PA_at` dérivée de la monotonie de `chainState`. -/
lemma PA_at_mono
    (hCnExt : CnExtensive Cn)
    {t u : Nat} (htu : t ≤ u)
    (hPA : PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t) :
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax u := by
  -- PA_at PAax n <=> PAax ⊆ (chainState ... n).Γ
  -- Donc si Γ(t) ⊆ Γ(u), alors PAax ⊆ Γ(t) => PAax ⊆ Γ(u)
  exact Set.Subset.trans hPA (chainState_mono hIdem hProvCn hCnExt htu)


/-- PA est “installé après un rang” dès qu’il apparaît une fois (par monotonie). -/
lemma PA_Eventually_of_exists
    (hCnExt : CnExtensive Cn)
    {t0 : Nat}
    (hPA0 :
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t0) :
    ∃ N, ∀ n, N ≤ n →
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax n := by
  refine ⟨t0, ?_⟩
  intro n hn
  have mono := PA_at_mono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn)
      (PAax := PAax) (hCnExt := hCnExt) (t := t0) (u := n)
  exact mono hn hPA0

/-
  THÉORÈME FINAL (objectif) :
  Plus d'hypothèse `PA_Eventually` externe !
  On la déduit de `witBC` + monotonie de chainState.
-/
theorem collatz_eventuallyNotAB_of_trilemma_and_consistency
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
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

  -- 0) Extraire une occurrence de PA_at depuis un witness PairPA (ici BC, N=0 suffit)
  rcases witBC 0 with ⟨t0, _, ht0⟩
  have hPA0 :
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t0 :=
    ht0.2

  -- 1) En déduire PA_Eventually grâce à la monotonie
  rcases (PA_Eventually_of_exists (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) (hCnExt := hCnExt)
            (PAax := PAax) hPA0)
    with ⟨N, hPA⟩

  -- 2) witnesses "simples" pour `times` et `strict_subseq_horns`
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

  -- 3) On reprend exactement la preuve structurelle
  refine ⟨N, ?_⟩
  intro k hkN hkAB

  let t :=
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB k

  let f : Nat → Nat :=
    fun m =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigmaCollatz seed) hIdem hProvCn wBC wAC wAB m

  have hstep : StrictStep f := by
    intro m
    simpa [f] using
      (times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigmaCollatz seed) (hIdem := hIdem) (hProvCn := hProvCn)
        wBC wAC wAB m)

  have hk_le_t : k ≤ t := by
    have hk_le_fk : k ≤ f k := le_of_strictStep f hstep k
    simpa [t, f] using hk_le_fk

  have hN_le_t : N ≤ t := Nat.le_trans hkN hk_le_t

  have hPA_t :
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t :=
    hPA t hN_le_t

  have hRoute :=
    hBridge t hPA_t

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
    simpa [sigmaCollatz, t, hkAB] using hNotRoute_raw

  exact hNotRoute hRoute

/-
  Corollaire (borne explicite) également mis à jour pour ne plus prendre hPAev.
-/
theorem collatz_AB_indices_bounded_of_trilemma_and_consistency
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
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
      hBridge witBC witAC witAB

  rcases hev with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro k hkAB
  have : ¬ B ≤ k := by
    intro hBk
    exact (hB k hBk) hkAB
  exact Nat.lt_of_not_ge this

end ABExtinction

end RevHalt.Trilemma
