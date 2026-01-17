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

/-- Helper for finding a witness in a list -/
def findInList (Γ : Set PropT) (p : PropT) : List ℕ → Option (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
  | [] => none
  | k :: ks =>
    if h : ChecksWC ChecksDerivation ChecksWitness decodeList Γ p k = true then
      some ⟨k, h⟩
    else
      findInList Γ p ks

/--
  Recherche bornée (totalement constructive) d'une WCDerivation.
  Utilise List.range pour éviter toute récursion explicite.
-/
def WCDerivation.findBounded
    (Γ : Set PropT) (p : PropT) (bound : ℕ) :
    Option (WCDerivation ChecksDerivation ChecksWitness decodeList Γ p) :=
  findInList ChecksDerivation ChecksWitness decodeList Γ p (List.range bound)

/--
  Completeness of bounded search: if a valid code exists within bound, search succeeds.
-/
theorem findInList_complete_aux
    (l : List ℕ)
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
    (hMem : d.code ∈ l) :
    (findInList ChecksDerivation ChecksWitness decodeList Γ p l).isSome := by
  induction l with
  | nil => contradiction
  | cons k ks ih =>
    unfold findInList
    by_cases hCheck : ChecksWC ChecksDerivation ChecksWitness decodeList Γ p k = true
    · simp [hCheck]
    · simp [hCheck]
      have hNe : k ≠ d.code := by
        intro hEq
        rw [hEq] at hCheck
        have hValid := d.valid
        rw [hValid] at hCheck
        contradiction
      have hInKs : d.code ∈ ks := List.mem_of_ne_of_mem hNe.symm hMem
      exact ih hInKs
theorem WCDerivation.findBounded_complete
    (Γ : Set PropT) (p : PropT) (bound : ℕ)
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
    (hBound : d.code < bound) :
    (WCDerivation.findBounded ChecksDerivation ChecksWitness decodeList Γ p bound).isSome := by
  have hMem : d.code ∈ List.range bound := List.mem_range.mpr hBound
  unfold findBounded
  exact findInList_complete_aux ChecksDerivation ChecksWitness decodeList (List.range bound) d hMem

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
