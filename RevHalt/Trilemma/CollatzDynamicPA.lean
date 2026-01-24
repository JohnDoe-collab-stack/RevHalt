/-
  CollatzDynamicPA.lean

  Objectif (aligné sur ton objectif) :
  - Collatz DANS le même fichier.
  - σ := sigmaOf seed (déterministe).
  - Démontrer une extinction *positive* de AB (borne explicite) à partir de :
      (1) Trilemme (via strict_subseq_horns / HornAB_at_time)
      (2) Consistance structurante : Pont  (PA_at t → RouteIIAt sur omegaΓ(chainState t))
  - Aucune hypothèse "si ça atteint 1".
  - Pas de Classical (au sens Choice), pas de noncomputable.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

/- =====================================================================
   1) DÉFINITIONS COLLATZ (Paramètre σ)
   ===================================================================== -/
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

/-- Alias pratique. -/
abbrev sigmaCollatz (seed : Nat) : Nat → Mode := Collatz.sigmaOf seed


/- =====================================================================
   2) PREUVE GÉNÉRIQUE (Indépendante de Collatz)
   Cette section établit l'extinction de AB pour TOUT σ, sous les
   hypothèses du Trilemme et de Consistance.
   ===================================================================== -/
section GenericSection
namespace Generic

variable {Provable : Set PropT → PropT → Prop}
variable {K : RHKit}
variable {Machine : Code → Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT → Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

-- Hypothèses structurelles
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
variable (hMono : ProvRelMonotone Provable)

-- Paramètres génériques
variable (PAax : Set PropT)
variable (sigma : Nat → Mode)

-- Pont (ne dépend pas de sigma)
def PA_implies_RouteIIAt : Prop :=
  ∀ t,
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t →
    RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
        (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t))

-- But générique : extinction AB pour sigma
def EventuallyNotAB (sigma : Nat → Mode) : Prop :=
  ∃ N, ∀ k, N ≤ k → sigma k ≠ Mode.AB

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
      -- Robust call to avoid unification issues
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
  exact Set.Subset.trans hPA (chainState_mono hIdem hProvCn hCnExt htu)

/-- PA est “installé après un rang” dès qu’il apparaît une fois. -/
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
      (hCnExt := hCnExt) (PAax := PAax) (t := t0) (u := n)
  exact mono hn hPA0

/--
  THÉORÈME GÉNÉRIQUE
  AB finit par s'éteindre pour tout σ compatible avec les témoins fournis.
-/
theorem eventuallyNotAB_of_trilemma_and_consistency
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBridge : PA_implies_RouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) (PAax := PAax))
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)) :
    EventuallyNotAB sigma := by

  -- 0) Extraire PA_at depuis un witness (BC)
  rcases witBC 0 with ⟨t0, _, ht0⟩
  have hPA0 :
      PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t0 :=
    ht0.2

  -- 1) PA_Eventually via monotonie
  rcases (PA_Eventually_of_exists (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) (hCnExt := hCnExt)
            (PAax := PAax) hPA0)
    with ⟨N, hPA⟩

  -- 2) Conversion en témoins simples
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

  -- 3) Démonstration par l'absurde sur les sous-suites
  refine ⟨N, ?_⟩
  intro k hkN hkAB

  let t :=
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigma) hIdem hProvCn wBC wAC wAB k

  let f : Nat → Nat :=
    fun m =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigma) hIdem hProvCn wBC wAC wAB m

  have hstep : StrictStep f := by
    intro m
    simpa [f] using
      (times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
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
      (sigma := sigma) hMono hCnExt hIdem hProvCn
      wBC wAC wAB k

  have hNotRoute :
      ¬ RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
          (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t)) := by
    simpa [t, hkAB] using hNotRoute_raw

  exact hNotRoute hRoute

end Generic
end GenericSection


/- =====================================================================
   3) APPLICATION À COLLATZ
   Collatz n'est qu'une instance particulière.
   ===================================================================== -/
namespace Collatz

variable {PropT : Type u} {Code : Type u}
variable {Provable : Set PropT → PropT → Prop}
variable {K : RHKit}
variable {Machine : Code → Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT → Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

/--
  Théorème d'extinction appliqué à Collatz.
  Démontre que la corne AB est bornée (finie).
-/
theorem collatz_AB_indices_bounded
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (hMono : ProvRelMonotone Provable) (hCnExt : CnExtensive Cn)
    (seed : Nat)
    (PAax : Set PropT)
    (hBridge : Generic.PA_implies_RouteIIAt (Provable := Provable) (K := K)
        (Machine := Machine) (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) (PAax := PAax))
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)) :
    ∃ B, ∀ k, sigmaOf seed k = Mode.AB → k < B := by
  -- Application du théorème générique avec sigma = sigmaOf seed
  have hGeneric : Generic.EventuallyNotAB (sigmaOf seed) :=
    Generic.eventuallyNotAB_of_trilemma_and_consistency
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn)
      (hMono := hMono) (hCnExt := hCnExt)
      (PAax := PAax) (sigma := sigmaOf seed)
      hBridge witBC witAC witAB

  rcases hGeneric with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro k hkAB
  have : ¬ B ≤ k := by
    intro hBk
    exact (hB k hBk) hkAB
  exact Nat.lt_of_not_ge this

end Collatz

end RevHalt.Trilemma

#print axioms RevHalt.Trilemma.Collatz.collatz_AB_indices_bounded
