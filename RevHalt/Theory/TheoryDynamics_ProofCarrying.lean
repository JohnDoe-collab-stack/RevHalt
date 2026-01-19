/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-!
# Witness-Carrying Provability

This module formalizes **witness-carrying** provability where proofs are
represented as verifiable codes that also carry a witness (certificate).

## Main definitions

* `WCCode` - A code representing a pair (proof, witness)
* `ChecksWC` - Decidable check that a code is valid (checks both proof and witness)
* `WCDerivation` - Structure bundling WCCode with validity proof
* `findBounded` - Computable search for a valid derivation
* `ProvableWC` - The resulting provability predicate (Nonempty WCDerivation)

## Key insight

Instead of just `Provable Γ p`, we work with an object that guarantees:
1. A proof exists (`ChecksDerivation`)
2. A witness exists and passes `ChecksWitness`

This effectively makes extraction (e.g. of a TSP tour) a projection of the proof object.
-/

namespace RevHalt.ProofCarrying.Witness

variable {PropT : Type*}

/-- A derivation code is a natural number encoding a proof tree. -/
abbrev DerivationCode := ℕ

/-- A witness-carrying code encodes a pair (proof, witness). -/
abbrev WCCode := ℕ

-- Aliases for Mathlib pairing
abbrev pair := Nat.pair
abbrev unpair_fst (n : ℕ) : ℕ := (Nat.unpair n).1
abbrev unpair_snd (n : ℕ) : ℕ := (Nat.unpair n).2

/-- Sépare le code (preuve, témoin). -/
def proofPart (c : WCCode) : DerivationCode := unpair_fst c
def witnessPart (c : WCCode) : ℕ := unpair_snd c

section Variables
variable (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)
variable (ChecksWitness : PropT → List ℕ → Bool)
variable (encodeList : List ℕ → ℕ)
variable (decodeList : ℕ → List ℕ)

/-- Décodage du témoin contenu dans le WCCode. -/
def decodeWitness (c : WCCode) : List ℕ :=
  decodeList (witnessPart c)

/--
  Le WCCode est valide si la preuve et le témoin checkent.
  C'est la conjonction de la validité déductive et de la validité sémantique du témoin.
-/
def ChecksWC (Γ : Set PropT) (p : PropT) (c : WCCode) : Bool :=
  (ChecksDerivation Γ p (proofPart c)) && (ChecksWitness p (decodeWitness decodeList c))

/--
  Une "dérivation witness-carrying" est juste un code qui passe ChecksWC.
-/
structure WCDerivation (Γ : Set PropT) (p : PropT) where
  code : WCCode
  valid : ChecksWC ChecksDerivation ChecksWitness decodeList Γ p code = true

/-- Extraction computable du témoin. -/
def WCDerivation.witness {Γ : Set PropT} {p : PropT}
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p) : List ℕ :=
  decodeWitness decodeList d.code

/--
  Recherche récursive bornée sans allocation de liste.
  Cherche un code valide k où `current ≤ k < bound`.
  Diminue le fuel pour assurer la terminaison.
-/
def findCode (Γ : Set PropT) (p : PropT) (bound : ℕ) (current : ℕ) : Option (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p) :=
  if h : current < bound then
    if hCheck : ChecksWC ChecksDerivation ChecksWitness decodeList Γ p current = true then
      some ⟨current, hCheck⟩
    else
      findCode Γ p bound (current + 1)
  else
    none
decreasing_by exact Nat.sub_succ_lt_self _ _ h

/--
  Recherche bornée (totalement constructive) d'une WCDerivation.
  Optimisée pour ne pas allouer une liste de taille `bound`.
-/
def WCDerivation.findBounded
    (Γ : Set PropT) (p : PropT) (bound : ℕ) :
    Option (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p) :=
  findCode ChecksDerivation ChecksWitness decodeList Γ p bound 0

/--
  Completeness of bounded search: if a valid code exists within bound, search succeeds.
-/
theorem findCode_complete
    (bound : ℕ)
    (current : ℕ)
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
    (hBound : d.code < bound)
    (hCurrent : current ≤ d.code) :
    (findCode ChecksDerivation ChecksWitness decodeList Γ p bound current).isSome := by
  -- Induction sur la distance (d.code - current)
  generalize hDist : d.code - current = k
  revert current
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro current hCurrent hDistEq
    unfold findCode
    -- current < bound est vrai car current ≤ d.code < bound
    have hLt : current < bound := Nat.lt_of_le_of_lt hCurrent hBound
    simp [hLt]
    by_cases hCheck : ChecksWC ChecksDerivation ChecksWitness decodeList Γ p current = true
    · simp [hCheck]
    · simp [hCheck]
      -- Si le code courant n'est pas bon, on avance
      have hNe : current ≠ d.code := by
        intro hEq
        rw [hEq] at hCheck
        have hValid := d.valid
        rw [hValid] at hCheck
        contradiction
      have hNextLE : current + 1 ≤ d.code := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hCurrent hNe)
      -- Fix: correct argument order and explicit arithmetic
      have hNextDist : d.code - (current + 1) < k := by
        rw [← hDistEq]
        apply Nat.sub_succ_lt_self
        exact Nat.lt_of_le_of_ne hCurrent hNe
      exact ih (d.code - (current + 1)) hNextDist (current + 1) hNextLE rfl

theorem WCDerivation.findBounded_complete
    (Γ : Set PropT) (p : PropT) (bound : ℕ)
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
    (hBound : d.code < bound) :
    (WCDerivation.findBounded ChecksDerivation ChecksWitness decodeList Γ p bound).isSome := by
  exact findCode_complete ChecksDerivation ChecksWitness decodeList bound 0 d hBound (Nat.zero_le _)

/--
  Propriété de monotonie du checker de dérivation.
  Nécessaire pour l'intégration dans la trajectoire RevHalt (ProvRelMonotone).
-/
def ChecksDerivationMonotone : Prop :=
  ∀ {Γ Γ' : Set PropT} {p : PropT} {c : DerivationCode},
    Γ ⊆ Γ' →
    ChecksDerivation Γ p c = true →
    ChecksDerivation Γ' p c = true

/--
  ChecksWC hérite de la monotonie de ChecksDerivation.
  (ChecksWitness ne dépend pas de Γ, donc il est trivialement monotone).
  Preuve robuste sans `simp`.
-/
theorem ChecksWC_monotone
    (hMono : ChecksDerivationMonotone ChecksDerivation)
    {Γ Γ' : Set PropT} (hSub : Γ ⊆ Γ')
    (p : PropT) (c : WCCode) :
    ChecksWC ChecksDerivation ChecksWitness decodeList Γ p c = true →
    ChecksWC ChecksDerivation ChecksWitness decodeList Γ' p c = true := by
  intro h
  simp only [ChecksWC, Bool.and_eq_true] at h ⊢
  refine ⟨?_, h.2⟩
  exact hMono hSub h.1

/--
  Provable Proof-Carrying (W) est monotone si le checker l'est.
-/
theorem WCDerivation_monotone
    (hMono : ChecksDerivationMonotone ChecksDerivation)
    {Γ Γ' : Set PropT} (hSub : Γ ⊆ Γ') (p : PropT) :
    Nonempty (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p) →
    Nonempty (WCDerivation ChecksDerivation ChecksWitness decodeList Γ' p) := by
  rintro ⟨d⟩
  exact ⟨{
    code := d.code
    valid := ChecksWC_monotone ChecksDerivation ChecksWitness decodeList hMono hSub p d.code d.valid
  }⟩

/--
  **ProvableWC**: The integration definition for RevHalt.
  Provability is defined as the existence of a valid witness-carrying derivation.
-/
def ProvableWC (Γ : Set PropT) (p : PropT) : Prop :=
  Nonempty (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)

/--
  ProvableWC satisfies the monotonicity requirement of TheoryDynamics.
-/
theorem ProvableWC_monotone
    (hMono : ChecksDerivationMonotone ChecksDerivation) :
    RevHalt.ProvRelMonotone (ProvableWC ChecksDerivation ChecksWitness decodeList) := by
  intro Γ Δ hSub p hProv
  exact WCDerivation_monotone ChecksDerivation ChecksWitness decodeList hMono hSub p hProv

end Variables

end RevHalt.ProofCarrying.Witness
