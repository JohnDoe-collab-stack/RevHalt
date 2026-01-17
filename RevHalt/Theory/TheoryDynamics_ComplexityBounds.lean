/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import Mathlib.Data.Nat.Basic

/-!
# Complexity Bounds for Theory Dynamics

This module defines the abstract notion of "polynomial time" within the RevHalt framework.
In the witness-carrying setting, "polynomial time" is formalized as a **polynomial bound**
on the size of the witness-carrying derivation required to prove a true statement.

## Main definitions

* `IsPoly` - Predicate for function `ℕ → ℕ` being polynomially bounded.
* `PolyPosWC` - Structure asserting that for every true instance in a language,
  there exists a valid witness-carrying derivation with code size bounded by a polynomial
  in the input size.

## Note on "Price of P"

This structure formalizes the "Price of P": achieving polynomial time corresponds to the
existence of a specialized `PolyPosWC` object, which acts as a certificate of efficiency
for the underlying proof system relative to a specific problem.
-/

namespace RevHalt.Complexity

open RevHalt.ProofCarrying.Witness

/--
  Predicate asserting that a function `f : ℕ → ℕ` is polynomially bounded.
  Definition: `∃ c d, ∀ n, f n ≤ c * n^d + c`
  We include `+ c` to handle the `n=0` case freely and ensure strictly positive constants if needed.
-/
def IsPoly (f : ℕ → ℕ) : Prop :=
  ∃ c d, ∀ n, f n ≤ c * (n ^ d) + c

/--
  **Polynomial Positive Witness-Carrying (PolyPosWC)**

  Asserts that a language (where "true" means `HasSolution`) admits
  short witness-carrying derivations.

  Parameters:
  * `Γ`: The theory state (context).
  * `ChecksDerivation`: The proof checker.
  * `ChecksWitness`: The witness checker (PropT → Witness → Bool).
  * `decodeList`: Decoder for witnesses (needed to interpret the generic derivation).
  * `size`: A measure of input size (`PropT → ℕ`).
  * `HasSolution`: The ground truth predicate for the problem (`PropT → Prop`).
  * `decodeProp`: Decodes the raw code (`PropT`, usually `ℕ`) into a structure to check solvability.
    If decoding fails, the condition is vacuously true or ignored.
-/
structure PolyPosWC
    {PropT : Type}
    (Γ : Set PropT)
    (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)
    (ChecksWitness : PropT → List ℕ → Bool)
    (decodeList : ℕ → List ℕ)
    (size : PropT → ℕ)
    (HasSolution : PropT → Prop)
    : Type where
  /-- The bounding function. -/
  B : ℕ → ℕ
  /-- The bound is polynomial. -/
  B_poly : IsPoly B
  /--
    Short Derivation Existence:
    For any valid instance code `p` that has a solution,
    there exists a valid WCDerivation ChecksDerivation ChecksWitness decodeList Γ p,
      whose code is bounded by `B(size p)`.
  -/
  pos_short :
    ∀ p : PropT, HasSolution p →
    ∃ d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p,
      d.code < B (size p)

/--
  **Monotonicity of Price of P**:
  If a polynomial bound exists for `Γ`, and `Γ ⊆ Γ'` (monotonic extension),
  then the *same* bound applies to `Γ'` (since proofs in `Γ` remain valid in `Γ'`).
-/
def PolyPosWC_monotone
    {PropT : Type}
    {Γ Γ' : Set PropT}
    {ChecksDerivation : Set PropT → PropT → DerivationCode → Bool}
    {ChecksWitness : PropT → List ℕ → Bool}
    {decodeList : ℕ → List ℕ}
    {size : PropT → ℕ}
    {HasSolution : PropT → Prop}
    (hMono : ChecksDerivationMonotone ChecksDerivation)
    (hSub : Γ ⊆ Γ')
    (poly : PolyPosWC Γ ChecksDerivation ChecksWitness decodeList size HasSolution) :
    PolyPosWC Γ' ChecksDerivation ChecksWitness decodeList size HasSolution := {
  B := poly.B
  B_poly := poly.B_poly
  pos_short := fun p hSol =>
    let ⟨d, hd_bound⟩ := poly.pos_short p hSol
    -- Lift derivation d from Γ to Γ'
    let d' : WCDerivation ChecksDerivation ChecksWitness decodeList Γ' p := {
      code := d.code
      valid := ChecksWC_monotone ChecksDerivation ChecksWitness decodeList hMono hSub p d.code d.valid
    }
    ⟨d', hd_bound⟩
}

end RevHalt.Complexity
