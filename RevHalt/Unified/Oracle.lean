/-
  RevHalt.Unified.Oracle

  Formalizes the "Framework as Oracle" concept.

  ## Core Idea

  From the perspective of an internal theory (with only access to `Provable`),
  the external semantic apparatus (`Truth`, `Halts`, `Rev0_K`) acts as a
  **translation oracle**: it provides verdicts that the theory cannot reconstruct
  internally without falling into incompleteness.

  This module makes explicit:
  1. What is a semantic oracle (`TruthOracle`)
  2. What it means to internalize an oracle (`InternalizesOracle`)
  3. Why Truth cannot be internalized (via T2 impossibility)
  4. Why the oracle strictly extends Provable, and its surplus is exactly the Gap

  ## Philosophical Interpretation

  The internal theory sees the framework's bridge mechanisms (HaltEncode, LR, etc.)
  as oracular: they provide correct semantic judgments that cannot be replicated
  by the theory's provability relation alone.

  This is not an oracle in the complexity sense (deciding membership), but rather
  a **semantic authority** that translates between referentials (external halting/truth
  vs internal provability).
-/

import RevHalt.Unified.Core
import RevHalt.Unified.MasterClosure
import RevHalt.Unified.System

namespace RevHalt_Unified

variable {Code PropT : Type}

/--
  A Truth Oracle: an external predicate on propositions that correctly captures Truth.

  From the internal theory's perspective, this is an "authority" that judges propositions
  semantically, beyond what `Provable` can determine.
-/
structure TruthOracle (ctx : EnrichedContext Code PropT) where
  /-- The oracle predicate: external judgment on propositions -/
  O : PropT → Prop
  /-- Correctness: the oracle agrees with semantic truth -/
  O_correct : ∀ p, O p ↔ ctx.Truth p

/--
  A theory **internalizes** an oracle if it can perfectly replicate the oracle's
  verdicts using only its provability relation.

  This requires:
  1. Completeness: every proposition is decidable
  2. Positive reflection: oracle-positive judgments are provable
  3. Negative reflection: oracle-negative judgments yield provable negations
-/
def InternalizesOracle (ctx : EnrichedContext Code PropT) (O : PropT → Prop) : Prop :=
  (∀ p, ctx.Provable p ∨ ctx.Provable (ctx.Not p)) ∧
  (∀ p, O p → ctx.Provable p) ∧
  (∀ p, ¬O p → ctx.Provable (ctx.Not p))

/--
  **Theorem: Truth Oracle Cannot Be Internalized**

  If a theory has a Truth oracle, then the theory cannot internalize this oracle.

  Proof: from T2 we get a true but unprovable `p`. Correctness gives `O p`,
  and positive reflection would force `Provable p`, contradiction.
-/
theorem oracle_not_internalizable
    (ctx : EnrichedContext Code PropT)
    (oracle : TruthOracle ctx) :
    ¬InternalizesOracle ctx oracle.O := by
  intro h_intern
  -- Only positive reflection is needed.
  obtain ⟨_, h_pos, _⟩ := h_intern
  obtain ⟨p, h_true, h_not_prov⟩ := true_but_unprovable_exists ctx
  have h_oracle_p : oracle.O p := (oracle.O_correct p).mpr h_true
  have h_prov : ctx.Provable p := h_pos p h_oracle_p
  exact h_not_prov h_prov

/--
  **Corollary (Bridge Is Oracular)**

  With a VerifiableContext, the bridge `Truth p ↔ Halts (LR ∅ p)` induces
  a canonical oracle `O p := Halts (LR ∅ p)`.

  That oracle cannot be internalized.
-/
theorem bridge_is_oracular
    (ctx : VerifiableContext Code PropT) :
    let oracle : TruthOracle ctx.toEnrichedContext := {
      O := fun p => Halts (ctx.LR ∅ p)
      O_correct := fun p => by
        constructor
        · intro hHalts; exact (ctx.h_bridge p).mpr hHalts
        · intro hTrue;  exact (ctx.h_bridge p).mp hTrue
    }
    ¬InternalizesOracle ctx.toEnrichedContext oracle.O := by
  intro oracle
  exact oracle_not_internalizable ctx.toEnrichedContext oracle

/--
  **Provable Implies Oracle (under soundness)**

  If provability is sound, then every provable proposition is recognized by the oracle.
-/
theorem provable_implies_oracle
    (ctx : EnrichedContext Code PropT)
    (oracle : TruthOracle ctx)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∀ p, ctx.Provable p → oracle.O p := by
  intro p hp
  exact (oracle.O_correct p).mpr (h_sound p hp)

/--
  **Oracle Surplus = GapTruth (pointwise)**

  The oracle’s "added value over Provable" at proposition `p` is:
    `oracle.O p ∧ ¬Provable p`

  This is equivalent (pointwise) to membership in `GapTruth`.
  This theorem does not require soundness.
-/
theorem oracle_surplus_iff_gapTruth
    (ctx : VerifiableContext Code PropT)
    (oracle : TruthOracle ctx.toEnrichedContext) :
    ∀ p, (oracle.O p ∧ ¬ctx.Provable p) ↔ p ∈ GapTruth ctx := by
  intro p
  rw [mem_GapTruth_iff]
  constructor
  · intro ⟨h_oracle, h_not_prov⟩
    have h_true : ctx.Truth p := (oracle.O_correct p).mp h_oracle
    exact ⟨h_true, h_not_prov⟩
  · intro ⟨h_true, h_not_prov⟩
    have h_oracle : oracle.O p := (oracle.O_correct p).mpr h_true
    exact ⟨h_oracle, h_not_prov⟩

/--
  **Meta-Theorem (Perfect): Oracle Authority = GapTruth + Coverage + Strictness**

  Under soundness, the oracle:
  1. Covers all provable propositions (`Provable ⊆ Oracle`)
  2. Has surplus over Provable exactly `GapTruth` (pointwise)
  3. Strictly extends Provable (surplus is nonempty)
-/
theorem oracle_authority_is_gap
    (ctx : VerifiableContext Code PropT)
    (oracle : TruthOracle ctx.toEnrichedContext)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    (∀ p, ctx.Provable p → oracle.O p) ∧
    (∀ p, (oracle.O p ∧ ¬ctx.Provable p) ↔ p ∈ GapTruth ctx) ∧
    (∃ p, oracle.O p ∧ ¬ctx.Provable p) := by
  refine ⟨?prov_to_oracle, ?surplus_eq_gap, ?strict⟩
  · intro p hp
    have hT : ctx.Truth p := h_sound p hp
    exact (oracle.O_correct p).mpr hT
  · intro p
    simpa using (oracle_surplus_iff_gapTruth (ctx := ctx) (oracle := oracle) p)
  · obtain ⟨p, hT, hNP⟩ := true_but_unprovable_exists ctx.toEnrichedContext
    exact ⟨p, (oracle.O_correct p).mpr hT, hNP⟩

end RevHalt_Unified
