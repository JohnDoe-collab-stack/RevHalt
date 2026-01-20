/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Pairing

/-!
# Separation Model: Price of P does not imply Collapse

This module constructs a formal counter-example to show that the "Price of P" hypothesis
(`PolyCompressionWC`) does *not* imply `Collapse` on its own.
This demonstrates that `Stability` is a necessary, independent hypothesis in the RevHalt bridge.

## The Model (Toy System)

We define a system where:
1.  **Truth** (`HasSolution`) is "Everything is true" (or simple standard truth).
    Here, we take `PropT := ℕ` and `HasSolution n := True`. All numbers are "true".
2.  **Provability** (`ProvableWC`) is restricted to **Even numbers**.
    `ChecksWC` accepts `c` as proof for `n` iff `c = n` and `n` is even.
3.  **Witnesses**: The witness for `n` is `n` itself.
4.  **Size**: The size of `n` is `n`.

## Results

*   **`PolyCompressionWC` holds**: For every provable `n` (which is even), the witness `n` has size `n`.
    Since `size(n) = n`, the witness size is bounded by the polynomial `P(x) = x`.
*   **`Collapse` fails**: There exist true statements (odd numbers) that are not provable.
    Thus, `HasSolution -> Provable` is false.

-/

namespace RevHalt.ProofComplexity.Separation

open RevHalt.ProofCarrying.Witness
open RevHalt.Complexity

/-- The type of propositions is just Natural Numbers. -/
abbrev ToyProp := ℕ

/-- Everything is "True" in this toy semantics. -/
def ToyTruth (_ : ToyProp) : Prop := True

/-- Size of a proposition is its value. -/
def sizeToy (n : ToyProp) : ℕ := n

/-- The Checker logic (Bool). -/
def checksToy (_ : Set ToyProp) (p : ToyProp) (c : WCCode) : Bool :=
  (c == p) && (p % 2 == 0)

/-- decodeList for Toy system (unused by checker). -/
def decodeListToy (_ : ℕ) : List ℕ := []

/-- The bounding function must account for pairing overhead. B(n) = pair n 0 + 1. -/
def B_toy (n : ℕ) : ℕ := Nat.pair n 0 + 1

lemma IsPoly_B_toy : IsPoly B_toy := by
  exists 3, 2
  intro n
  unfold B_toy
  -- Use exact library lemma: pair n 0 < (max n 0 + 1)^2
  have h_pair := Nat.pair_lt_max_add_one_sq n 0
  rw [Nat.max_eq_left (Nat.zero_le n)] at h_pair
  -- h_pair: pair n 0 < (n+1)^2
  have h_bound : Nat.pair n 0 + 1 ≤ (n + 1) * (n + 1) + 1 := by
    rw [Nat.pow_two] at h_pair
    apply Nat.add_le_add_right (Nat.le_of_lt h_pair)
  calc
    Nat.pair n 0 + 1
      ≤ n^2 + 2*n + 2 := by ring_nf at h_bound ⊢; exact h_bound
    _ ≤ 3 * n^2 + 3 := by
      cases n <;> nlinarith


/-- Soundness: Anything proven is True (trivial since everything is True). -/
theorem toy_sound (Γ : Set ToyProp) :
  ∀ p, (∃ c, checksToy Γ p c) → ToyTruth p := by
  intros p _
  exact True.intro

/--
  **Theorem 1**: This system satisfies `PolyPosWC` (Polynomial Witness Complexity).
  Bound is Quadratic.
-/
def Toy_satisfies_PriceOfP (Γ : Set ToyProp) :
  PolyPosWC Γ (fun _ => checksToy Γ) (fun _ _ => true) decodeListToy sizeToy (fun p => ∃ c, checksToy Γ p c) := {
  B := B_toy
  B_poly := IsPoly_B_toy
  pos_short := by
    intro p hProvable
    match hProvable with
    | ⟨c, hc⟩ =>
      -- hc : checksToy Γ p c = true
      have h_and : (c == p) = true ∧ (p % 2 == 0) = true := by
        rw [checksToy, Bool.and_eq_true] at hc
        exact hc
      have heq : c = p := by
        rw [beq_iff_eq] at h_and
        exact h_and.1

      -- We construct the derivation explicitly using Nat.pair c 0
      let d : WCDerivation (fun _ => checksToy Γ) (fun _ _ => true) decodeListToy Γ p := {
        code := Nat.pair c 0,
        valid := by
          simp only [ChecksWC, proofPart]
          -- check unpair using simp (standard mathlib behavior)
          -- unpair_fst (pair c 0) = c
          simp only [unpair_fst, Nat.unpair_pair]
          rw [Bool.and_true]
          exact hc
      }

      exists d
      -- Bound check: d.code < B_toy (sizeToy p)
      show Nat.pair c 0 < B_toy (sizeToy p)
      simp [B_toy, sizeToy, heq]

}

/--
  **Theorem 2**: This system does NOT Collapse.
-/
theorem Toy_does_not_Collapse (Γ : Set ToyProp) :
  ¬ (∀ p, ToyTruth p → ∃ c, checksToy Γ p c) := by
  intro hCollapse
  -- Consider p = 1.
  have hTrue : ToyTruth 1 := True.intro
  have hProvable : ∃ c, checksToy Γ 1 c := hCollapse 1 hTrue
  match hProvable with
  | ⟨c, hc⟩ =>
    rw [checksToy, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hc
    have hEven : 1 % 2 = 0 := hc.2
    -- 1 % 2 is 1, not 0. Contradiction.
    contradiction

/--
  **Main Result**: `PolyPosWC` does not imply `Collapse`.
-/
theorem PriceOfP_does_not_imply_Collapse :
  ∃ (PropT : Type)
    (Γ : Set PropT)
    (Checks : Set PropT → PropT → DerivationCode → Bool)
    (size : PropT → ℕ)
    (Truth : PropT → Prop),
    Nonempty (PolyPosWC Γ Checks (fun _ _ => true) decodeListToy size (fun p => ∃ c, Checks Γ p c)) ∧
    ¬ (∀ p, Truth p → ∃ c, Checks Γ p c) := by
  exists ToyProp, ∅, (fun Γ => checksToy Γ), sizeToy, ToyTruth
  constructor
  · exact Nonempty.intro (Toy_satisfies_PriceOfP ∅)
  · apply Toy_does_not_Collapse

end RevHalt.ProofComplexity.Separation
