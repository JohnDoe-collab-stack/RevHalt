/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.ProofComplexity.Correspondence

/-!
# Proof Complexity: Simulation / Robustness

This module adds a standard robustness tool for Objective A:
polynomial-time simulation between Propositional Proof Systems (PPS) and the
transfer of polynomial boundedness along such simulations.

The intended use is to make the "Price of P" hypotheses less encoding-dependent:
if a checker-induced PPS is polynomially bounded, and it polynomially simulates
another PPS (or vice-versa, depending on direction), then the target PPS is also
polynomially bounded.
-/

namespace RevHalt.Complexity

/-! Small closure lemmas for `IsPoly`. -/

theorem pow_succ_le_two_pow_mul_add_one (n k : ℕ) :
    (n + 1) ^ k ≤ (2 ^ k) * (n ^ k + 1) := by
  by_cases hn : n = 0
  · subst hn
    -- LHS = 1. RHS ≥ 2^k ≥ 1.
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hpow' : (0 + 1) ^ k ≤ 2 ^ k := by
      -- (0+1)^k = 1
      simpa using hpow
    have hmul : 2 ^ k ≤ (2 ^ k) * ((0 ^ k) + 1) :=
      Nat.le_mul_of_pos_right (2 ^ k) (Nat.succ_pos (0 ^ k))
    exact le_trans hpow' hmul
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    -- n + 1 ≤ 2*n for n>0
    have hsucc_le : n + 1 ≤ 2 * n := by
      -- reduce to `n + 1 ≤ n + n`
      have : n + 1 ≤ n + n :=
        Nat.succ_le_iff.mpr (Nat.add_lt_add_left hnpos n)
      -- rewrite `2*n` as `n+n`
      rw [Nat.two_mul n]
      exact this
    -- raise to k: (n+1)^k ≤ (2*n)^k = 2^k * n^k
    have hpow : (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left hsucc_le k
    have hpow' : (n + 1) ^ k ≤ (2 ^ k) * (n ^ k) := by
      -- rewrite RHS of `hpow` using `(a*b)^k = a^k * b^k`
      have h := hpow
      -- `(2*n)^k = 2^k * n^k`
      rw [Nat.mul_pow 2 n k] at h
      exact h
    have hmono : (2 ^ k) * (n ^ k) ≤ (2 ^ k) * (n ^ k + 1) :=
      Nat.mul_le_mul_left (2 ^ k) (Nat.le_add_right _ _)
    exact le_trans hpow' hmono

theorem IsPoly.mul_const (k : ℕ) (f : ℕ → ℕ) (hf : IsPoly f) : IsPoly (fun n => k * f n) := by
  rcases hf with ⟨c, d, hc⟩
  refine ⟨k * c, d, ?_⟩
  intro n
  calc
    k * f n ≤ k * (c * (n ^ d) + c) := Nat.mul_le_mul_left k (hc n)
    _ = (k * c) * (n ^ d) + (k * c) := by
          simp [Nat.mul_add, Nat.mul_assoc]

theorem IsPoly.add_const (k : ℕ) (f : ℕ → ℕ) (hf : IsPoly f) : IsPoly (fun n => f n + k) := by
  rcases hf with ⟨c, d, hc⟩
  refine ⟨c + k, d, ?_⟩
  intro n
  calc
    f n + k ≤ (c * (n ^ d) + c) + k := Nat.add_le_add_right (hc n) k
    _ = c * (n ^ d) + (c + k) := by simp [Nat.add_assoc, Nat.add_comm]
    _ ≤ (c + k) * (n ^ d) + (c + k) := by
          refine Nat.add_le_add_right ?_ _
          have : c ≤ c + k := Nat.le_add_right _ _
          exact Nat.mul_le_mul_right _ this

theorem IsPoly.pow_const (d : ℕ) : IsPoly (fun n => n ^ d) := by
  refine ⟨1, d, ?_⟩
  intro n
  -- n^d ≤ 1*(n^d) ≤ 1*(n^d)+1
  have h1 : n ^ d ≤ 1 * (n ^ d) := by
    exact le_of_eq (Nat.one_mul (n ^ d)).symm
  have h2 : 1 * (n ^ d) ≤ 1 * (n ^ d) + 1 := Nat.le_add_right _ _
  exact le_trans h1 h2

theorem IsPoly.comp (g f : ℕ → ℕ) (hg : IsPoly g) (hf : IsPoly f) :
    IsPoly (fun n => g (f n)) := by
  rcases hf with ⟨cf, df, hf⟩
  rcases hg with ⟨cg, dg, hg⟩
  refine ⟨cg * (cf ^ dg) * (2 ^ dg) + cg, df * dg, ?_⟩
  intro n
  -- Rewrite the `hf` bound as `f n ≤ cf * (n^df + 1)`.
  have hf' : f n ≤ cf * (n ^ df + 1) := by
    have hEq : cf * (n ^ df + 1) = cf * (n ^ df) + cf := by
      calc
        cf * (n ^ df + 1) = cf * (n ^ df) + cf * 1 := Nat.mul_add cf (n ^ df) 1
        _ = cf * (n ^ df) + cf := by rw [Nat.mul_one]
    have : cf * (n ^ df) + cf ≤ cf * (n ^ df + 1) := by
      -- rewrite the goal using `hEq`
      rw [hEq]
    exact le_trans (hf n) this

  -- Bound `(f n)^dg` by a polynomial in `n`.
  have hpow_succ : (n ^ df + 1) ^ dg ≤ (2 ^ dg) * (n ^ (df * dg) + 1) := by
    have h0 := pow_succ_le_two_pow_mul_add_one (n ^ df) dg
    -- rewrite `(n^df)^dg` as `n^(df*dg)`
    have hPowMul : (n ^ df) ^ dg = n ^ (df * dg) := (Nat.pow_mul n df dg).symm
    -- apply the rewrite in the RHS of `h0`
    simpa [hPowMul] using h0

  have hpow :
      (f n) ^ dg ≤ (cf ^ dg) * ((2 ^ dg) * (n ^ (df * dg) + 1)) := by
    have hpow_f : (f n) ^ dg ≤ (cf * (n ^ df + 1)) ^ dg :=
      Nat.pow_le_pow_left hf' dg
    calc
      (f n) ^ dg ≤ (cf * (n ^ df + 1)) ^ dg := hpow_f
      _ = (cf ^ dg) * (n ^ df + 1) ^ dg := by
            -- `(a*b)^k = a^k * b^k`
            exact Nat.mul_pow cf (n ^ df + 1) dg
      _ ≤ (cf ^ dg) * ((2 ^ dg) * (n ^ (df * dg) + 1)) := by
            exact Nat.mul_le_mul_left _ hpow_succ

  -- Apply the polynomial bound for `g` at the argument `f n`.
  have hg_fn : g (f n) ≤ cg * ((f n) ^ dg) + cg := hg (f n)
  have hg_fn' :
      g (f n) ≤ cg * ((cf ^ dg) * ((2 ^ dg) * (n ^ (df * dg) + 1))) + cg := by
    have hmul : cg * ((f n) ^ dg) ≤ cg * ((cf ^ dg) * ((2 ^ dg) * (n ^ (df * dg) + 1))) :=
      Nat.mul_le_mul_left _ hpow
    exact le_trans hg_fn (Nat.add_le_add_right hmul _)

  -- Package constants and finish by algebraic monotonicity.
  let E : ℕ := n ^ (df * dg)
  let K : ℕ := cg * (cf ^ dg) * (2 ^ dg)
  let C : ℕ := K + cg

  have hKg :
      cg * ((cf ^ dg) * ((2 ^ dg) * (n ^ (df * dg) + 1))) =
        K * (E + 1) := by
    -- Reassociate into `K * (E + 1)` without `simp`/`simpa` (axiom-safe).
    dsimp [K, E]
    set X : ℕ := n ^ (df * dg) + 1
    -- goal is now: `cg * (cf^dg * (2^dg * X)) = cg * cf^dg * 2^dg * X`
    calc
      cg * ((cf ^ dg) * ((2 ^ dg) * X)) = (cg * (cf ^ dg)) * ((2 ^ dg) * X) := by
        exact (Nat.mul_assoc cg (cf ^ dg) ((2 ^ dg) * X)).symm
      _ = ((cg * (cf ^ dg)) * (2 ^ dg)) * X := by
        exact (Nat.mul_assoc (cg * (cf ^ dg)) (2 ^ dg) X).symm
      _ = cg * (cf ^ dg) * (2 ^ dg) * X := by
        rfl

  have hBound1 : g (f n) ≤ K * (E + 1) + cg := by
    -- Rewrite the polynomial factor into `K*(E+1)` without `simpa`.
    have h := hg_fn'
    rw [hKg] at h
    exact h

  have hExpand : K * (E + 1) + cg = K * E + C := by
    -- Expand `K*(E+1)` and fold `C = K + cg` without brittle rewrites.
    dsimp [C]
    calc
      K * (E + 1) + cg = (K * E + K * 1) + cg := by
        rw [Nat.mul_add K E 1]
      _ = (K * E + K) + cg := by
        rw [Nat.mul_one]
      _ = K * E + (K + cg) := by
        exact Nat.add_assoc (K * E) K cg

  have hBound2 : g (f n) ≤ K * E + C := by
    exact le_trans hBound1 (le_of_eq hExpand)

  have hFinal : K * E + C ≤ C * E + C := by
    have hK_le_C : K ≤ C := Nat.le_add_right K cg
    have hmul : K * E ≤ C * E := Nat.mul_le_mul_right E hK_le_C
    exact Nat.add_le_add_right hmul C

  exact le_trans hBound2 hFinal


end RevHalt.Complexity

namespace RevHalt.ProofComplexity

open RevHalt.Complexity

/-! Simulation between PPS and transfer of polynomial boundedness. -/

structure PPSSimulates
    {PropT : Type}
    {IsTautology : PropT → Prop}
    {Proof₁ Proof₂ : Type}
    {size₁ : Proof₁ → ℕ}
    {size₂ : Proof₂ → ℕ}
    (Sys₁ : PropositionalProofSystem IsTautology Proof₁ size₁)
    (Sys₂ : PropositionalProofSystem IsTautology Proof₂ size₂) : Type where
  /-- Proof translation. -/
  map : Proof₁ → Proof₂
  /-- A polynomial upper bound on translated proof sizes, given as explicit data. -/
  bound : ℕ → ℕ
  bound_c : ℕ
  bound_d : ℕ
  bound_spec : ∀ n, bound n ≤ bound_c * (n ^ bound_d) + bound_c
  /-- If Sys₁ verifies, Sys₂ verifies the translated proof. -/
  verify_map : ∀ x π, Sys₁.Verifier x π = true → Sys₂.Verifier x (map π) = true
  /-- Size of translated proofs is controlled by `bound`. -/
  size_map : ∀ π, size₂ (map π) ≤ bound (size₁ π)

def PolynomiallyBoundedPPS_of_simulation
    {PropT : Type}
    {IsTautology : PropT → Prop}
    {Proof₁ Proof₂ : Type}
    {size₁ : Proof₁ → ℕ}
    {size₂ : Proof₂ → ℕ}
    {sizeProp : PropT → ℕ}
    {Sys₁ : PropositionalProofSystem IsTautology Proof₁ size₁}
    {Sys₂ : PropositionalProofSystem IsTautology Proof₂ size₂}
    (h₁ : PolynomiallyBoundedPPS Sys₁ sizeProp)
    (sim : PPSSimulates Sys₁ Sys₂) :
    PolynomiallyBoundedPPS Sys₂ sizeProp := by
  let P₂ : ℕ → ℕ := fun n => sim.bound_c * (h₁.P n) ^ sim.bound_d + sim.bound_c
  refine {
    P := P₂
    is_poly := ?_
    short_proofs := ?_
  }
  · have hPow : IsPoly (fun n => (h₁.P n) ^ sim.bound_d) :=
      IsPoly.comp (fun m => m ^ sim.bound_d) h₁.P (IsPoly.pow_const sim.bound_d) h₁.is_poly
    have hMul : IsPoly (fun n => sim.bound_c * (h₁.P n) ^ sim.bound_d) :=
      IsPoly.mul_const sim.bound_c _ hPow
    simpa [P₂] using IsPoly.add_const sim.bound_c _ hMul
  · intro x hx
    rcases h₁.short_proofs x hx with ⟨π, hVer, hSize⟩
    refine ⟨sim.map π, sim.verify_map x π hVer, ?_⟩
    have hpow_le :
        (size₁ π) ^ sim.bound_d ≤ (h₁.P (sizeProp x)) ^ sim.bound_d :=
      Nat.pow_le_pow_left hSize sim.bound_d
    calc
      size₂ (sim.map π) ≤ sim.bound (size₁ π) := sim.size_map π
      _ ≤ sim.bound_c * (size₁ π) ^ sim.bound_d + sim.bound_c := sim.bound_spec (size₁ π)
      _ ≤ sim.bound_c * (h₁.P (sizeProp x)) ^ sim.bound_d + sim.bound_c := by
            refine Nat.add_le_add_right ?_ _
            exact Nat.mul_le_mul_left _ hpow_le
      _ = P₂ (sizeProp x) := by rfl

end RevHalt.ProofComplexity
