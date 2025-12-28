/-
  RevHalt.Theory.InfiniteGaps

  ═══════════════════════════════════════════════════════════════════════════════
  INFINITE GAPS API (Structural Hypotheses)
  ═══════════════════════════════════════════════════════════════════════════════
  This module defines the STRUCTURAL REQUIREMENTS to obtain infinite gaps.
  It does NOT construct them directly (which requires specific encoding details).

  Structures provided:
  1. `TaggedProposition`: hypothesis that we can tag props injectively.
  2. `GapFamily`: hypothesis that we have an indexed family of witnesses.
  3. `CodePairing`: hypothesis that we have injective pairing on Code.

  Usage:
  - Instantiate `TaggedProposition` for your specific logic (e.g. PA).
  - Or instantiate `CodePairing` for your specific coding (e.g. Gödel).
  - Then use `taggedGapFamily` or `gapFamily_infinite` to get the result.
  ═══════════════════════════════════════════════════════════════════════════════
-/

import RevHalt.Theory.Complementarity
import RevHalt.Bridge.Context

namespace RevHalt.Theory

open RevHalt

/-!
## Tagging Strategy

Instead of proving `e_n ≠ e_m` (difficult), we:
1. Tag propositions with an index `n`
2. Construct a family of propositions that are structurally distinct
3. Show each is true but unprovable

The key insight: the diagonal construction can be parameterized.
-/

variable {Code PropT : Type}

/-- A tagging function embeds an index into a proposition. -/
structure TaggedProposition (PropT : Type) where
  Tag : ℕ → PropT → PropT
  tag_inj : ∀ n m p, Tag n p = Tag m p → n = m

/-- Given a context and a base gap witness, we can construct a tagged family. -/
def taggedGapFamily
    (ctx : EnrichedContext Code PropT)
    (tag : TaggedProposition PropT)
    (base : GapWitness ctx)
    (n : ℕ) : PropT :=
  tag.Tag n (GapWitness.prop base)

/-- The tagged family produces distinct propositions.
    (This is structural distinctness, not requiring code inequality.) -/
theorem taggedGapFamily_distinct
    (ctx : EnrichedContext Code PropT)
    (tag : TaggedProposition PropT)
    (base : GapWitness ctx)
    (n m : ℕ) (h : taggedGapFamily ctx tag base n = taggedGapFamily ctx tag base m) :
    n = m :=
  tag.tag_inj n m (GapWitness.prop base) h

/-!
## Alternative: Indexed Diagonal Construction

If the system supports parameterized fixed points, we can construct a family
of diagonal codes `e_n` where each gives a distinct gap.
-/

/-- A family of gap witnesses indexed by ℕ. -/
structure GapFamily (ctx : EnrichedContext Code PropT) where
  gap : ℕ → GapWitness ctx
  props_distinct : ∀ n m, GapWitness.prop (gap n) = GapWitness.prop (gap m) → n = m

/-- From a GapFamily, we get infinitely many distinct true-but-unprovable propositions. -/
theorem gapFamily_infinite (ctx : EnrichedContext Code PropT) (fam : GapFamily ctx) :
    ∀ n, ∃ p, ctx.Truth p ∧ ¬ctx.Provable p ∧
      (∀ m, m ≠ n → GapWitness.prop (fam.gap m) ≠ GapWitness.prop (fam.gap n)) := by
  intro n
  refine ⟨GapWitness.prop (fam.gap n), ?_, ?_, ?_⟩
  · exact GapWitness.truth (fam.gap n)
  · exact GapWitness.not_provable (fam.gap n)
  · intro m hne heq
    exact hne (fam.props_distinct n m heq.symm).symm

/-!
## Construction via Pairing

Given a single diagonal code `e₀` that produces a gap, and an injective pairing
function `pair : ℕ → Code → Code`, we can construct a family.

This is the standard technique: use Kleene's fixed point with a parameter.
-/

/-- Injective pairing on codes. -/
structure CodePairing (Code : Type) where
  pair : ℕ → Code → Code
  pair_inj_fst : ∀ n m c, pair n c = pair m c → n = m

/-- Given a base code and pairing, construct a code family. -/
def codeFamilyFromPairing
    (pairing : CodePairing Code)
    (base : Code)
    (n : ℕ) : Code :=
  pairing.pair n base

/-- The code family is injective in the index. -/
theorem codeFamilyFromPairing_inj
    (pairing : CodePairing Code)
    (base : Code)
    (n m : ℕ) (h : codeFamilyFromPairing pairing base n = codeFamilyFromPairing pairing base m) :
    n = m :=
  pairing.pair_inj_fst n m base h

/-!
## Summary

This module provides:
1. `TaggedProposition` - structural tagging for distinctness
2. `GapFamily` - indexed family of gap witnesses
3. `CodePairing` - injective pairing for code families

These tools allow constructing infinite gap families without `InfiniteS1` postulates.
The key is that distinctness comes from the tagging/pairing structure, not from
proving code inequality directly.
-/

end RevHalt.Theory
