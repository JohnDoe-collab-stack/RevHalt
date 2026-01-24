/-
  CollatzDynamicPA.lean

  Objectif (aligné sur ton objectif) :
  - Collatz DANS le même fichier.
  - σ := sigmaOf seed (déterministe).
  - Démontrer une extinction *positive* de AB (borne explicite) à partir de :
      (1) Une instance valide de `CollatzInstance` (Trilemme + Pont).
  - Architecture "Zero-Injection" stricte : via import GenericExtinction.
-/

import RevHalt.Trilemma.GenericExtinction

namespace RevHalt.Trilemma

universe u

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

end Collatz

/- =====================================================================
   2) APPLICATION À L'INSTANCE
   Collatz n'est qu'une instance particulière.
   Le théorème consomme une structure d'instance "Paquet Cadeau".
   ===================================================================== -/
namespace App

/--
  Théorème d'extinction appliqué à Collatz.
  Démontre que la corne AB est bornée (finie) pour TOUTE instance valide.
-/
theorem collatz_AB_indices_bounded
    (I : Generic.CollatzInstance)
    (seed : Nat) :
    ∃ B, ∀ k, Collatz.sigmaOf seed k = Mode.AB → k < B := by
  -- Application du théorème générique purement logique
  have hGeneric : Generic.EventuallyNotAB (Collatz.sigmaOf seed) :=
    Generic.eventuallyNotAB_of_instance (Collatz.sigmaOf seed) (I := I)

  rcases hGeneric with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro k hkAB
  have : ¬ B ≤ k := by
    intro hBk
    exact (hB k hBk) hkAB
  exact Nat.lt_of_not_ge this

end App
end RevHalt.Trilemma

#print axioms RevHalt.Trilemma.App.collatz_AB_indices_bounded
