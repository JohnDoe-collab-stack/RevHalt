import RevHalt.Theory.Complementarity
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.ArithTest

Arithmetic test (pure, without Splitter) demonstrating the core thesis:

> The detection of the kernel forces a non-internalizable frontier.

## Setup

- **S2 (post-splitter)** := `{ p | S.Provable p }` (the "absorbable" internal corpus)
- **S3** := `S2 ∪ S1` (minimal extension adding the frontier)
- **Key theorem**: `MissingFromS2(S3) = S1`

This captures exactly: "kernel detection forces a non-internalizable frontier".

## What this establishes (pure arithmetic)

- "post-splitter = S2" is a canonical choice (provable)
- the "non-absorbable" frontier is exactly `MissingFromS2(S3)`
- if the frontier exists, you have strictly more truths in S3 than in S2

-/

namespace RevHalt.ArithTest

open RevHalt

variable {Code PropT : Type}
variable (S : RevHalt.ComplementaritySystem Code PropT)
variable (Truth : PropT → Prop)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. The canonical "post-splitter": S2 = Provable
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The canonical "post-splitter": everything that S can internalize. -/
def S2prov : Set PropT := { p | S.Provable p }

/-- Trivial property: membership in S2prov implies provable. -/
lemma S2prov_mem_imp_provable : ∀ p, p ∈ S2prov (S := S) → S.Provable p := by
  intro p hp; exact hp

/-- If S is sound w.r.t. Truth, then S2prov is sound (in the T3 sense). -/
lemma S2prov_sound (h_sound : ∀ p, S.Provable p → Truth p) :
    ∀ p ∈ S2prov (S := S), Truth p := by
  intro p hp; exact h_sound p hp

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. S3 = S2 ∪ S1 with S2 := Provable
-- ═══════════════════════════════════════════════════════════════════════════════

variable (encode_halt : Code → PropT)

/-- S3 := S2 ∪ S1, with S2 := Provable. -/
abbrev S3prov : Set PropT := RevHalt.S3Set S (S2prov (S := S)) encode_halt

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. Key theorem "Subtraction": MissingFromS2(S3) = S1
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Canonical version of missing_equals_S1**:
If post-splitter = "what the system can prove", then the part added by extension (S3)
that remains *unprovable* is **exactly** the frontier (S1).

So yes, you get formally: "S1 is what S2 cannot absorb".
-/
theorem missing_from_provable_equals_S1 :
    RevHalt.MissingFromS2 S (S3prov (S := S) encode_halt)
      = RevHalt.S1Set S encode_halt := by
  -- apply the generic theorem with trivial hS2_prov
  have h := RevHalt.missing_equals_S1 (S := S)
    (S2 := (S2prov (S := S))) (encode_halt := encode_halt)
    (hS2_prov := (S2prov_mem_imp_provable (S := S)))
  exact h

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4. Structural consequence: if S1 ≠ ∅ then S2 ⊂ S3
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Inclusion is always true. -/
theorem S2prov_subset_S3prov :
    (S2prov (S := S)) ⊆ (S3prov (S := S) encode_halt) := by
  intro p hp
  exact Or.inl hp

/--
**Core structural theorem**:
If S1 is non-empty, then S2prov ⊂ S3prov (strict subset).

This says exactly what we want: **as soon as the frontier exists**,
the "post-splitter" (provable) is strictly too small.
-/
theorem S2prov_ssubset_S3prov_of_S1_nonempty
    (hS1 : (RevHalt.S1Set S encode_halt).Nonempty) :
    (S2prov (S := S)) ⊂ (S3prov (S := S) encode_halt) := by
  refine Set.ssubset_iff_subset_ne.2 ?_
  refine ⟨S2prov_subset_S3prov (S := S) (encode_halt := encode_halt), ?_⟩
  intro hEq
  rcases hS1 with ⟨p, hpS1⟩
  -- p ∈ S3 (because S3 = S2 ∪ S1)
  have hpS3 : p ∈ (S3prov (S := S) encode_halt) := Or.inr hpS1
  -- so p ∈ S2 if S3 = S2, contradiction because p ∈ S1 implies ¬Provable
  have hpS2 : p ∈ (S2prov (S := S)) := by rw [hEq]; exact hpS3
  rcases hpS1 with ⟨e, hpEq, _hKit, hUnprov⟩
  have : S.Provable (encode_halt e) := by
    have hp2 : S.Provable p := hpS2
    rw [hpEq] at hp2
    exact hp2
  exact hUnprov this

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5. Where does S1 ≠ ∅ come from "without Splitter"?
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
Two paths, complementary:

### (A) "Local" path (witness)

If you have an `e` and two proofs:
- `hKit : Rev0_K S.K (S.Machine e)` (certification)
- `hUnprov : ¬ S.Provable (encode_halt e)` (non-internalizable)

then `S1Set_nonempty_of_witness` gives you `S1 ≠ ∅` immediately.

### (B) "Structural" path (forced incompleteness)

`frontier_necessary` captures precisely the "stable incompleteness" point:

> if the system had a form of negative completeness + the corresponding semi-decidability,
> then **S1Eff.Nonempty** is forced,
> otherwise you'd construct an `InternalHaltingPredicate` and contradict T2.

This is the invariant: **you cannot uniformize kernel detection**
in a total and correct internal predicate.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6. Corollary: combining the paths
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Corollary (witness path)**:
Given a witness `e` that is Kit-certified but unprovable,
the post-splitter S2prov is strictly smaller than S3prov.
-/
theorem strict_extension_of_witness
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    (S2prov (S := S)) ⊂ (S3prov (S := S) encode_halt) := by
  have hS1 : (RevHalt.S1Set S encode_halt).Nonempty :=
    RevHalt.S1Set_nonempty_of_witness S encode_halt e hKit hUnprov
  exact S2prov_ssubset_S3prov_of_S1_nonempty S encode_halt hS1

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7. The Kernel Path: kernel detection → forced frontier → strict extension
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Corollary (kernel path)**:
If the system can internalize *negative* information from the kernel test
(`up (Machine c) = ⊥`), then T2 forces a non-empty frontier, hence a strict extension
S2prov ⊂ S3prov.

This is the literal "kernel detection forces a non-internalizable frontier" route.

The invariant is **not S1**, but the **impossibility** of uniformly internalizing
kernel detection — S1 is the forced manifestation of this obstruction.
-/
theorem strict_extension_forced_by_kernel
    (encode_halt : Code → PropT)
    -- Negative completeness stated *as kernel internalization*
    (h_neg_complete_up :
      ∀ c : RevHalt.Code,
        RevHalt.up (RevHalt.Machine c) = ⊥ →
          S.Provable (S.Not (encode_halt (S.dec c))))
    -- Semi-decidability data (same as frontier_necessary)
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (h_semidec :
      ∀ c : RevHalt.Code,
        S.Provable (S.Not (encode_halt (S.dec c))) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    (S2prov (S := S)) ⊂ (S3prov (S := S) encode_halt) := by
  -- First rewrite the kernel form into the ¬Rev0 form expected by frontier_necessary
  have h_neg_complete :
      ∀ c : RevHalt.Code,
        ¬ Rev0_K S.K (RevHalt.Machine c) →
          S.Provable (S.Not (encode_halt (S.dec c))) := by
    intro c hnot
    have hup : RevHalt.up (RevHalt.Machine c) = ⊥ :=
      (RevHalt.KitStabilizes_iff_up_eq_bot S.K S.h_canon (RevHalt.Machine c)).1 hnot
    exact h_neg_complete_up c hup

  have hS1Eff : (RevHalt.S1Eff S encode_halt).Nonempty :=
    RevHalt.frontier_necessary (S := S) (encode_halt := encode_halt)
      h_neg_complete f hf h_semidec

  have hS1 : (RevHalt.S1Set S encode_halt).Nonempty := by
    -- Use the definitional equivalence S1Eff = S1Set
    rw [← RevHalt.S1Eff_eq_S1Set (S := S) (encode_halt := encode_halt)]
    exact hS1Eff

  exact S2prov_ssubset_S3prov_of_S1_nonempty (S := S) (encode_halt := encode_halt) hS1

end RevHalt.ArithTest

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8. ArithNat: The "Fully on ℕ" Version
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## ArithNat: Projecting the Frontier onto ℕ

S1 is a set of sentences (PropT). The "witnesses on ℕ" are the codes (Gödel numbers) of
the e that generate these frontier sentences.

`FrontierNat ⊆ ℕ` contains concrete natural numbers.
Each n ∈ FrontierNat comes with a witness e (no classical choice required).

The equivalence `S1Set.Nonempty ↔ FrontierNat.Nonempty` shows that
"the law manifests in integers" = FrontierNat.Nonempty.
-/

namespace RevHalt.ArithNat

open RevHalt

variable {Code PropT : Type}
variable [Encodable Code]
variable (S : RevHalt.ComplementaritySystem Code PropT)
variable (encode_halt : Code → PropT)

/-- Gödelization: each `e : Code` has a natural code. -/
def codeNat : Code → ℕ := Encodable.encode

/--
The *arithmetic* frontier: the integers `n` that code an `e`
such that the Kit certifies `e` (positive side here) but `S` cannot internalize `encode_halt e`.
-/
def FrontierNat : Set ℕ :=
  { n | ∃ e : Code,
      Encodable.encode e = n ∧
      Rev0_K S.K (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) }

/-- If S1Set is non-empty, then FrontierNat is non-empty. -/
theorem frontierNat_nonempty_of_S1_nonempty :
    (RevHalt.S1Set S encode_halt).Nonempty →
    (FrontierNat S encode_halt).Nonempty := by
  intro hS1
  rcases hS1 with ⟨p, hp⟩
  rcases hp with ⟨e, hpEq, hKit, hUnprov⟩
  refine ⟨Encodable.encode e, ?_⟩
  refine ⟨e, rfl, hKit, ?_⟩
  exact hUnprov

/-- If FrontierNat is non-empty, then S1Set is non-empty. -/
theorem S1_nonempty_of_frontierNat_nonempty :
    (FrontierNat S encode_halt).Nonempty →
    (RevHalt.S1Set S encode_halt).Nonempty := by
  intro hN
  rcases hN with ⟨n, e, _hne, hKit, hUnprov⟩
  refine ⟨encode_halt e, ?_⟩
  exact ⟨e, rfl, hKit, hUnprov⟩

/-- Equivalence: S1Set.Nonempty ↔ FrontierNat.Nonempty -/
theorem S1_iff_frontierNat :
    (RevHalt.S1Set S encode_halt).Nonempty ↔
    (FrontierNat S encode_halt).Nonempty :=
  ⟨frontierNat_nonempty_of_S1_nonempty S encode_halt,
   S1_nonempty_of_frontierNat_nonempty S encode_halt⟩

/-- Purely ℕ formulation: there exists a frontier natural code. -/
def GapOnNat : Prop :=
  (FrontierNat S encode_halt).Nonempty

/-- Unfold the formulation: "there exists an integer n that codes a frontier e". -/
theorem GapOnNat_iff :
    GapOnNat S encode_halt ↔
    ∃ n : ℕ, ∃ e : Code,
      Encodable.encode e = n ∧
      Rev0_K S.K (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) := by
  constructor
  · intro ⟨n, e, hn, hk, hu⟩
    exact ⟨n, e, hn, hk, hu⟩
  · intro ⟨n, e, hn, hk, hu⟩
    exact ⟨n, e, hn, hk, hu⟩

/--
**The Conservation Law on ℕ**:
The obstruction lives as a subset of ℕ (FrontierNat) that cannot be emptied
by any "admissible improvement" (in the sense of T2/T3).
-/
theorem conservation_on_nat
    (hS1 : (RevHalt.S1Set S encode_halt).Nonempty) :
    GapOnNat S encode_halt := by
  exact (S1_iff_frontierNat S encode_halt).mp hS1

end RevHalt.ArithNat

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.ArithTest.S2prov
#print axioms RevHalt.ArithTest.S2prov_mem_imp_provable
#print axioms RevHalt.ArithTest.S2prov_sound
#print axioms RevHalt.ArithTest.missing_from_provable_equals_S1
#print axioms RevHalt.ArithTest.S2prov_subset_S3prov
#print axioms RevHalt.ArithTest.S2prov_ssubset_S3prov_of_S1_nonempty
#print axioms RevHalt.ArithTest.strict_extension_of_witness
