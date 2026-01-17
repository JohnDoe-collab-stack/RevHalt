/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under the MIT license.
-/
import RevHalt.Theory.TheoryDynamics

/-!
# Proof-Carrying Provability

This module formalizes **proof-carrying** provability where proofs are
represented as verifiable codes rather than abstract propositions.

## Main definitions

* `DerivationCode` - A code representing a derivation
* `ChecksDerivation` - Decidable check that a code is a valid derivation
* `Derivation` - Structure bundling code with validity proof

## Key insight

Instead of `Provable Γ p : Prop`, we work with:
```lean
Derivation Γ p := { code : ℕ // ChecksDerivation Γ p code = true }
```

This makes proof extraction computable.
-/

namespace RevHalt.ProofCarrying

variable {PropT : Type*}

/--
  A derivation code is a natural number encoding a proof tree.
  The encoding depends on the specific proof system.
-/
abbrev DerivationCode := ℕ

/--
  Decidable check that `code` is a valid derivation of `p` from `Γ`.

  This is the core computational primitive: given a code, we can
  mechanically verify if it represents a valid proof.

  Implementation note: The actual checking function depends on the
  proof system. Here we axiomatize it via variable.
-/
variable (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)

/--
  A derivation is a code together with a proof that it checks.
  This is the proof-carrying structure.
-/
structure Derivation (Γ : Set PropT) (p : PropT) where
  /-- The derivation code -/
  code : DerivationCode
  /-- Proof that the code is valid -/
  valid : ChecksDerivation Γ p code = true

/--
  Soundness hypothesis: If a derivation exists, the proposition is provable.
  This connects proof-carrying to the abstract Provable predicate.
-/
def DerivationSoundness (Provable : Set PropT → PropT → Prop) : Prop :=
  ∀ Γ p, Derivation ChecksDerivation Γ p → Provable Γ p

/--
  Completeness hypothesis: If p is provable, a derivation exists.
  This is the key bridge for extraction.
-/
def DerivationCompleteness (Provable : Set PropT → PropT → Prop) : Prop :=
  ∀ Γ p, Provable Γ p → ∃ d : Derivation ChecksDerivation Γ p, True

/--
  If ChecksDerivation is decidable for all codes (which it is by construction),
  we can search for a derivation by enumeration.

  This returns `some d` if a derivation is found within the search bound,
  `none` otherwise.
-/
def Derivation.findBounded (Γ : Set PropT) (p : PropT) (bound : ℕ) :
    Option (Derivation ChecksDerivation Γ p) :=
  let rec search (k : ℕ) : Option (Derivation ChecksDerivation Γ p) :=
    if k ≥ bound then none
    else if hcheck : ChecksDerivation Γ p k = true
         then some ⟨k, hcheck⟩
         else search (k + 1)
  search 0

/--
  Given an explicit derivation code that we know is valid, construct the Derivation.
-/
def Derivation.ofCode (Γ : Set PropT) (p : PropT) (code : DerivationCode)
    (hvalid : ChecksDerivation Γ p code = true) : Derivation ChecksDerivation Γ p :=
  ⟨code, hvalid⟩

end RevHalt.ProofCarrying
