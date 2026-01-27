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
import Mathlib.Data.Nat.Factorization.Basic

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

lemma iter_eq_iterate_step (k seed : Nat) :
    iter k seed = (step^[k]) seed := by
  induction k generalizing seed with
  | zero =>
      simp [iter]
  | succ k ih =>
      simp [iter, ih]

lemma iter_add (a b seed : Nat) :
    iter (a + b) seed = iter b (iter a seed) := by
  -- `Function.iterate_add_apply` gives the composition law for iteration.
  -- We pick the order `b + a` and rewrite using commutativity of addition.
  simpa [iter_eq_iterate_step, Nat.add_comm] using
    (Function.iterate_add_apply step b a seed)

lemma step_of_mod2_eq_zero {n : Nat} (hn : n % 2 = 0) :
    step n = n / 2 := by
  simp [step, hn]

lemma step_ne_zero_of_ne_zero {n : Nat} (hn : n ≠ 0) : step n ≠ 0 := by
  by_cases hmod : n % 2 = 0
  · -- even: `n/2 = 0` would imply `n < 2`, hence `n = 0` (since `n` is even)
    have : n / 2 ≠ 0 := by
      intro hdiv
      have hnlt : n < 2 := by
        -- `n / 2 = 0` iff `n < 2`
        simpa [Nat.div_eq_zero_iff_lt, Nat.succ_pos'] using hdiv
      -- If `n < 2` and `n % 2 = 0`, then `n = 0`.
      cases n with
      | zero => exact hn rfl
      | succ n =>
          cases n with
          | zero =>
              -- n = 1 contradicts `n % 2 = 0`
              simp at hmod
          | succ n =>
              -- n >= 2 contradicts `n < 2`
              exact (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hnlt).elim
    simpa [step, hmod] using this
  · -- odd: `3*n+1` is never 0
    simpa [step, hmod] using (Nat.succ_ne_zero (3 * n))

lemma iter_ne_zero_of_ne_zero (k n : Nat) (hn : n ≠ 0) : iter k n ≠ 0 := by
  induction k generalizing n with
  | zero =>
      simpa [iter] using hn
  | succ k ih =>
      have hs : step n ≠ 0 := step_ne_zero_of_ne_zero hn
      simpa [iter] using ih (step n) hs

lemma iter_two_pow_mul (k m : Nat) :
    iter k (2 ^ k * m) = m := by
  induction k generalizing m with
  | zero =>
      simp [iter]
  | succ k ih =>
      -- Show the (k+1)-step start value is even, so `step` is division by 2.
      have hmod : (2 ^ (k + 1) * m) % 2 = 0 := by
        -- `2^(k+1)*m = 2*(2^k*m)` is visibly a multiple of 2.
        have : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        -- Rewrite and let `simp` close the mod-2 goal.
        simpa [this]
      have hstep : step (2 ^ (k + 1) * m) = (2 ^ (k + 1) * m) / 2 :=
        step_of_mod2_eq_zero hmod
      have hdiv : (2 ^ (k + 1) * m) / 2 = 2 ^ k * m := by
        -- `2^(k+1) * m = (2^k * m) * 2`, and `(x*2)/2 = x`.
        calc
          (2 ^ (k + 1) * m) / 2
              = ((2 ^ k * m) * 2) / 2 := by
                  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 2 ^ k * m := by
                  simp
      -- One step reduces to the k-step claim.
      simp [iter, hstep, hdiv, ih]

lemma iter_two_pow (k : Nat) :
    iter k (2 ^ k) = 1 := by
  -- `2^k = 2^k * 1`
  simpa using (iter_two_pow_mul k 1)

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

/- =====================================================================
   3) CONCLUSION COLLATZ (borne AB -> atteint 1)
   ===================================================================== -/

private theorem no_AB_after_of_bound
    (seed : Nat)
    (hBound : ∃ B, ∀ k, Collatz.sigmaOf seed k = Mode.AB → k < B) :
    ∃ B, ∀ k, B ≤ k → Collatz.sigmaOf seed k ≠ Mode.AB := by
  rcases hBound with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro k hkBk hkAB
  have hkLt : k < B := hB k hkAB
  exact Nat.not_lt_of_ge hkBk hkLt

/--
Si les indices `k` tels que `sigmaOf seed k = AB` sont bornés,
alors la trajectoire Collatz atteint `1` (au moins une fois),
à condition que `seed ≠ 0` (le cas `seed = 0` est un point fixe pair).
-/
theorem collatz_reaches_one_of_AB_indices_bounded
    (seed : Nat) (hseed : seed ≠ 0)
    (hBound : ∃ B, ∀ k, Collatz.sigmaOf seed k = Mode.AB → k < B) :
    ∃ n, Collatz.iter n seed = 1 := by
  rcases no_AB_after_of_bound seed hBound with ⟨B, hNoAB⟩

  -- Let x0 be the state at time B.
  let x0 : Nat := Collatz.iter B seed

  -- x0 is either 1 or even, because `sigmaOf seed B ≠ AB`.
  have hx0_cases : x0 = 1 ∨ x0 % 2 = 0 := by
    have hσ : Collatz.sigmaOf seed B ≠ Mode.AB := hNoAB B (Nat.le_refl B)
    by_cases h1 : x0 = 1
    · exact Or.inl h1
    · have : x0 % 2 = 0 := by
        by_contra hmod
        have hAB : Collatz.sigmaOf seed B = Mode.AB := by
          -- If x0 ≠ 1 and x0 is odd, sigma is AB.
          simp [Collatz.sigmaOf, x0, h1, hmod]
        exact hσ hAB
      exact Or.inr this

  -- Helper: `x0 ≠ 0` from `seed ≠ 0` (Collatz step never hits 0 from a nonzero seed).
  have hx0_ne_zero : x0 ≠ 0 := by
    simpa [x0] using (Collatz.iter_ne_zero_of_ne_zero B seed hseed)

  -- If x0 = 1, we are done with n = B.
  cases hx0_cases with
  | inl hx1 =>
      refine ⟨B, ?_⟩
      simpa [x0, hx1]
  | inr _ =>
      -- Decompose x0 as `2^k * m` with m odd.
      rcases Nat.exists_eq_two_pow_mul_odd hx0_ne_zero with ⟨k, m, hmOdd, hx0⟩
      -- If m ≠ 1, then at time B+k we hit an odd != 1, hence sigma = AB: contradiction.
      have hm_must_be_one : m = 1 := by
        by_contra hm_ne_one
        -- Compute iter (B+k) seed = m.
        have hIterBk : Collatz.iter (B + k) seed = m := by
          calc
            Collatz.iter (B + k) seed
                = Collatz.iter k x0 := by
                    simpa [x0] using (Collatz.iter_add B k seed)
            _ = Collatz.iter k (2 ^ k * m) := by
                    simpa [hx0]
            _ = m := by
                    simpa using (Collatz.iter_two_pow_mul k m)
        -- Show sigmaOf seed (B+k) = AB, using oddness and `m ≠ 1`.
        have hm_mod : m % 2 ≠ 0 := by
          rcases hmOdd with ⟨t, rfl⟩
          simp
        have hAB : Collatz.sigmaOf seed (B + k) = Mode.AB := by
          simp [Collatz.sigmaOf, hIterBk, hm_ne_one, hm_mod]
        -- Contradiction with "no AB after B".
        exact (hNoAB (B + k) (Nat.le_add_right B k)) hAB
      -- So x0 = 2^k, hence iter (B+k) seed = 1.
      have hx0_pow : x0 = 2 ^ k := by
        -- x0 = 2^k * m and m = 1
        simpa [hm_must_be_one] using hx0
      refine ⟨B + k, ?_⟩
      -- iter (B+k) seed = iter k x0 = iter k (2^k) = 1
      calc
        Collatz.iter (B + k) seed
            = Collatz.iter k x0 := by
                simpa [x0] using (Collatz.iter_add B k seed)
        _ = Collatz.iter k (2 ^ k) := by
                simpa [hx0_pow]
        _ = 1 := by
                simpa using (Collatz.iter_two_pow k)

/--
Version “conjecture Collatz” (pour les entiers positifs) :
pour tout `seed`, la trajectoire de `seed+1` atteint 1.
-/
theorem collatz_conjecture_of_instance
    (I : Generic.CollatzInstance) :
    ∀ seed : Nat, ∃ n, Collatz.iter n (seed + 1) = 1 := by
  intro seed
  have hBound : ∃ B, ∀ k, Collatz.sigmaOf (seed + 1) k = Mode.AB → k < B :=
    collatz_AB_indices_bounded (I := I) (seed := seed + 1)
  have hpos : seed + 1 ≠ 0 := Nat.succ_ne_zero _
  exact collatz_reaches_one_of_AB_indices_bounded (seed := seed + 1) hpos hBound

end App
end RevHalt.Trilemma

#print axioms RevHalt.Trilemma.App.collatz_AB_indices_bounded
