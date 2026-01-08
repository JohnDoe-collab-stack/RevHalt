import RevHalt.Theory.Stabilization
import RevHalt.Theory.ArithTest
import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.ArithTwo

The "two-sided" version of the ArithTest, fully grounded on ℕ.
This captures exactly:

"Kit verdict (positive = halt, negative = kernel) but non-absorbable by S2prov".

## Structure

1. **FrontierNatTwo**: The concrete set of integers on ℕ that manifest the obstruction.
2. **S1TwoKitSet**: The sentence-level frontier (two-sided).
3. **S3TwoKitSet**: The minimal extension S2prov ∪ S1TwoKitSet.
4. **Kernel Link**: The negative branch explicitly means `up T = ⊥`.

This formalizes the "conservation law" perspective:
The obstruction to internalizing kernel detection manifests as a concrete frontier on ℕ.
-/

namespace RevHalt.ArithNatTwo

open RevHalt

variable {Code PropT : Type}
variable (S : RevHalt.ComplementaritySystem Code PropT)
variable (encode_halt : Code → PropT)

section Definitions
variable (encode_not_halt : Code → PropT)

section Encodable
variable [Encodable Code]

/-- Natural code of a program `e`. -/
def codeNat : Code → ℕ := Encodable.encode

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. Frontier on ℕ: FrontierNatTwo
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Two-sided arithmetic frontier on ℕ:
Integers `n` coding an `e` such that the Kit decides (halt or kernel),
but the corresponding statement is not internalizable (`¬ Provable`).
-/
def FrontierNatTwo : Set ℕ :=
  { n | ∃ e : Code,
      codeNat e = n ∧
      (
        (Rev0_K S.K (S.Machine e) ∧ ¬ S.Provable (encode_halt e))
        ∨
        (KitStabilizes S.K (S.Machine e) ∧ ¬ S.Provable (encode_not_halt e))
      ) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. Sentence-level Frontier: S1TwoKitSet
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two-sided sentence-level frontier driven by the Kit. -/
def S1TwoKitSet : Set PropT :=
  { p | ∃ e : Code,
      (
        (p = encode_halt e ∧ Rev0_K S.K (S.Machine e) ∧ ¬ S.Provable (encode_halt e))
        ∨
        (p = encode_not_halt e ∧ KitStabilizes S.K (S.Machine e) ∧ ¬ S.Provable (encode_not_halt e))
      ) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. Post-splitter = S2prov, Extension = S3TwoKitSet
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Canonical post-splitter: everything that `S` can internalize. -/
def S2prov : Set PropT := { p | S.Provable p }

/-- Minimal extension by the two-sided frontier. -/
def S3TwoKitSet : Set PropT := S2prov (S := S) ∪ S1TwoKitSet (S := S) encode_halt encode_not_halt

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4. Equivalence on ℕ: Non-emptiness Bridge
-- ═══════════════════════════════════════════════════════════════════════════════

theorem frontierNatTwo_nonempty_of_S1TwoKit_nonempty :
    (S1TwoKitSet (S := S) encode_halt encode_not_halt).Nonempty →
    (FrontierNatTwo (S := S) encode_halt encode_not_halt).Nonempty := by
  intro h
  rcases h with ⟨p, hp⟩
  rcases hp with ⟨e, hcases⟩
  refine ⟨codeNat e, ?_⟩
  refine ⟨e, rfl, ?_⟩
  cases hcases with
  | inl hpos =>
      -- p = encode_halt e ∧ Rev0_K ... ∧ ¬Provable (encode_halt e)
      exact Or.inl ⟨hpos.2.1, hpos.2.2⟩
  | inr hneg =>
      -- p = encode_not_halt e ∧ KitStabilizes ... ∧ ¬Provable (encode_not_halt e)
      exact Or.inr ⟨hneg.2.1, hneg.2.2⟩

theorem S1TwoKit_nonempty_of_frontierNatTwo_nonempty :
    (FrontierNatTwo (S := S) encode_halt encode_not_halt).Nonempty →
    (S1TwoKitSet (S := S) encode_halt encode_not_halt).Nonempty := by
  intro h
  rcases h with ⟨n, e, _hne, hcases⟩
  cases hcases with
  | inl hpos =>
      refine ⟨encode_halt e, ?_⟩
      refine ⟨e, Or.inl ?_⟩
      exact ⟨rfl, hpos.1, hpos.2⟩
  | inr hneg =>
      refine ⟨encode_not_halt e, ?_⟩
      refine ⟨e, Or.inr ?_⟩
      exact ⟨rfl, hneg.1, hneg.2⟩

end Encodable

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5. Explicit Kernel Link: Negative branch = Ker(up)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
The negative branch implies membership in the kernel of `up`.
This is exactly "kernel detection ⇒ frontier".
-/
theorem neg_branch_implies_kernel
    (hK : DetectsMonotone S.K)
    {e : Code}
    (hneg : KitStabilizes S.K (S.Machine e)) :
    up (S.Machine e) = ⊥ := by
  -- Key theorem: KitStabilizes K T ↔ up T = ⊥
  exact (KitStabilizes_iff_up_eq_bot S.K hK (S.Machine e)).1 hneg

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6. Structural Consequence: Post-splitter too small
-- ═══════════════════════════════════════════════════════════════════════════════

/--
If the frontier exists (on ℕ), then S2prov is strictly smaller than the extension.
-/
theorem S2prov_ssubset_S3TwoKit_of_frontier_nonempty
    (h : (S1TwoKitSet (S := S) encode_halt encode_not_halt).Nonempty) :
    (S2prov (S := S)) ⊂ (S3TwoKitSet (S := S) encode_halt encode_not_halt) := by
  refine Set.ssubset_iff_subset_ne.2 ?_
  refine ⟨?subset, ?ne⟩
  · intro p hp
    exact Or.inl hp
  · intro hEq
    rcases h with ⟨p, hpS1⟩
    have hpS3 : p ∈ S3TwoKitSet (S := S) encode_halt encode_not_halt := Or.inr hpS1
    have hpS2 : p ∈ S2prov (S := S) := by
      -- if S3 = S2, then p ∈ S2
      rw [hEq]; exact hpS3
    -- hpS2 : Provable p
    have hProv : S.Provable p := hpS2
    -- but hpS1 gives ¬Provable p (by cases)
    rcases hpS1 with ⟨e, hcases⟩
    cases hcases with
    | inl hpos =>
        -- p = encode_halt e ∧ ... ∧ ¬Provable (encode_halt e)
        have : ¬ S.Provable p := by
          -- rewrite p = encode_halt e
          intro hp
          have hp' : S.Provable (encode_halt e) := by
            have heq : p = encode_halt e := hpos.1
            rw [heq] at hp
            exact hp
          exact hpos.2.2 hp'
        exact (this hProv).elim
    | inr hneg =>
        have : ¬ S.Provable p := by
          intro hp
          have hp' : S.Provable (encode_not_halt e) := by
            have heq : p = encode_not_halt e := hneg.1
            rw [heq] at hp
            exact hp
          exact hneg.2.2 hp'
        exact (this hProv).elim

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7. Conservation Law on ℕ (Full Two-Sided)
-- ═══════════════════════════════════════════════════════════════════════════════

section Conservation

open Nat.Partrec

/--
**Conservation Law (Two-Sided) on ℕ**:

If you try to internalize *uniformly* the two verdicts of the Kit
(by having both negative completeness and semi-decidability compatible with T2),
you inevitably contradict T2.

Therefore, `FrontierNatTwo` is necessarily non-empty. This proves that the
existence of "frontier integers" is forced by the impossibility of uniform internalization.
-/
theorem conservation_nat_two_sided_forced
    [Encodable Code] [Primcodable Code]
    -- Semi-decidability of the provability of negation on integers (as usual)
    -- This is the only "admissible technology" we assume: the system can look for proofs.
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (h_semidec : ∀ n : RevHalt.Code,
        S.Provable (S.Not (encode_halt (S.dec n))) ↔ (∃ x : Nat, x ∈ (f n) 0)) :
    (FrontierNatTwo (S := S) encode_halt (fun e => S.Not (encode_halt e))).Nonempty := by
  classical
  by_contra hEmpty
  -- If frontier is empty, then for every n, n ∉ FrontierNatTwo
  rw [Set.not_nonempty_iff_eq_empty] at hEmpty

  -- This implies completeness on both branches!
  -- 1. Positive Completeness: If Kit says HALT, then Provable(halt)
  have h_pos_complete : ∀ e : Code,
      Rev0_K S.K (S.Machine e) → S.Provable (encode_halt e) := by
    intro e hRev
    by_cases hp : S.Provable (encode_halt e)
    · exact hp
    · -- Then `encode e ∈ FrontierNatTwo` (positive branch), contradiction
      have : Encodable.encode e ∈ FrontierNatTwo (S := S) encode_halt (fun e => S.Not (encode_halt e)) := by
        refine ⟨e, rfl, Or.inl ?_⟩
        exact ⟨hRev, hp⟩
      rw [hEmpty] at this
      cases this

  -- 2. Negative Completeness: If Kit says KERNEL, then Provable(not halt)
  have h_neg_complete : ∀ e : Code,
      KitStabilizes S.K (S.Machine e) → S.Provable (S.Not (encode_halt e)) := by
    intro e hStab
    by_cases hp : S.Provable (S.Not (encode_halt e))
    · exact hp
    · -- Then `encode e ∈ FrontierNatTwo` (negative branch), contradiction
      have : Encodable.encode e ∈ FrontierNatTwo (S := S) encode_halt (fun e => S.Not (encode_halt e)) := by
        refine ⟨e, rfl, Or.inr ?_⟩
        exact ⟨hStab, hp⟩
      rw [hEmpty] at this
      cases this

  -- 3. Construct the Impossible InternalHaltingPredicate
  let H : RevHalt.Code → PropT := fun n => encode_halt (S.dec n)

  have h_total : ∀ n : RevHalt.Code,
      S.Provable (H n) ∨ S.Provable (S.Not (H n)) := by
    intro n
    -- Decide using the Kit via the isomorphism
    let M_n := RevHalt.Machine n
    cases Classical.em (Rev0_K S.K M_n) with
    | inl hRev =>
        -- Positive branch
        have hMeq : S.Machine (S.dec n) = M_n := by
          rw [S.machine_eq (S.dec n), S.enc_dec n]
        rewrite [← hMeq] at hRev
        left
        exact h_pos_complete (S.dec n) hRev
    | inr hNotRev =>
        -- Negative branch (Kernel)
        have hStab_n : KitStabilizes S.K M_n := hNotRev -- definitionally
        have hMeq : S.Machine (S.dec n) = M_n := by
          rw [S.machine_eq (S.dec n), S.enc_dec n]
        rewrite [← hMeq] at hStab_n
        right
        -- Apply h_neg_complete
        -- h_neg_complete proves Provable (S.Not (encode_halt (S.dec n)))
        -- Which is exactly Provable (S.Not (H n))
        exact h_neg_complete (S.dec n) hStab_n

  have h_correct : ∀ n : RevHalt.Code,
      Rev0_K S.K (RevHalt.Machine n) → S.Provable (H n) := by
    intro n hRev
    have hMeq : S.Machine (S.dec n) = RevHalt.Machine n := by
       rw [S.machine_eq (S.dec n), S.enc_dec n]
    rewrite [← hMeq] at hRev
    exact h_pos_complete (S.dec n) hRev

  have h_complete : ∀ n : RevHalt.Code,
      ¬ Rev0_K S.K (RevHalt.Machine n) → S.Provable (S.Not (H n)) := by
    intro n hNotRev
    have hStab_n : KitStabilizes S.K (RevHalt.Machine n) := hNotRev
    have hMeq : S.Machine (S.dec n) = RevHalt.Machine n := by
       rw [S.machine_eq (S.dec n), S.enc_dec n]
    rewrite [← hMeq] at hStab_n
    -- encode_not_halt is S.Not (encode_halt)
    -- So we need to prove S.Provable (S.Not (encode_halt (S.dec n)))
    -- H n is encode_halt (S.dec n)
    -- h_neg_complete proves Provable (encode_not_halt (S.dec n))
    -- encode_not_halt (S.dec n) def= S.Not (encode_halt (S.dec n))
    exact h_neg_complete (S.dec n) hStab_n

  let I : InternalHaltingPredicate S.toImpossibleSystem S.K := {
    H := H
    total := h_total
    correct := h_correct
    complete := h_complete
    f := f
    f_partrec := hf
    semidec := h_semidec
  }

  -- 4. Contradiction with T2
  have : False :=
    (T2_impossibility S.toImpossibleSystem S.K S.h_canon) ⟨I, trivial⟩

  exact this.elim

end Conservation

end Definitions

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8. Dynamic Chain: The Gap Persists
-- ═══════════════════════════════════════════════════════════════════════════════

section IterChain

/--
A "Partition" of indices for the infinite frontier.
This allows us to chunk the infinite frontier into manageable pieces for iteration.
-/
structure Partition (ι : Type) where
  Parts : ℕ → Set ι

/-- A "chunk" of the frontier at step n, indexed by a partition. -/
def FrontierChunk (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) (n : ℕ) : Set PropT :=
  { p | ∃ i ∈ partition.Parts n, p = encode_halt (indep.family i) }

/-- Cumulative frontier up to step n. -/
def FrontierUpTo (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) (n : ℕ) : Set PropT :=
  { p | ∃ k ≤ n, p ∈ FrontierChunk (S := S) (encode_halt := encode_halt) indep partition k }

/-- Chain of extensions: S3_{≤n} := S2prov ∪ FrontierUpTo n. -/
def S3_chain (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) (n : ℕ) : Set PropT :=
  (S2prov (S := S)) ∪ FrontierUpTo (S := S) (encode_halt := encode_halt) indep partition n

/-- Monotonicity of the cumulative frontier. -/
theorem FrontierUpTo_mono (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) :
    ∀ {n m}, n ≤ m →
      FrontierUpTo (S := S) (encode_halt := encode_halt) indep partition n ⊆
      FrontierUpTo (S := S) (encode_halt := encode_halt) indep partition m := by
  intro n m hnm p hp
  rcases hp with ⟨k, hkn, hk⟩
  exact ⟨k, le_trans hkn hnm, hk⟩

/-- Monotonicity of the chain S3_{≤n}. -/
theorem S3_chain_mono (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) :
    ∀ {n m}, n ≤ m →
      S3_chain (S := S) (encode_halt := encode_halt) indep partition n ⊆
      S3_chain (S := S) (encode_halt := encode_halt) indep partition m := by
  intro n m hnm p hp
  cases hp with
  | inl hp2 => exact Or.inl hp2
  | inr hpF =>
      exact Or.inr (FrontierUpTo_mono (S := S) (encode_halt := encode_halt) indep partition hnm hpF)

/--
The Gap Persists:
Even though S3_n grows, S2prov remains fixed (or grows much slower if we were to extend the system).
Crucially, the elements in FrontierUpTo n are *never* in S2prov (by definition of S1).
-/
theorem frontier_chunks_disjoint_S2prov (indep : InfiniteS1 (S := S) encode_halt)
    (partition : Partition indep.Index) (n : ℕ) :
    Disjoint (S2prov S) (FrontierUpTo S encode_halt indep partition n) := by
  rw [Set.disjoint_left]
  intro p hS2 hFrontier
  rcases hFrontier with ⟨k, _, hChunk⟩
  rcases hChunk with ⟨i, _, hp_eq⟩
  -- p is in S2prov implies Provable p
  have hProv : S.Provable p := hS2
  -- p = encode_halt (family i)
  rw [hp_eq] at hProv
  -- But family i is in S1 (via InfiniteS1), so it is unprovable
  have hUnprov : ¬ S.Provable (encode_halt (indep.family i)) :=
    indep.unprovable i
  exact hUnprov hProv

end IterChain

end RevHalt.ArithNatTwo

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.ArithNatTwo.FrontierNatTwo
#print axioms RevHalt.ArithNatTwo.S1TwoKitSet
#print axioms RevHalt.ArithNatTwo.frontierNatTwo_nonempty_of_S1TwoKit_nonempty
#print axioms RevHalt.ArithNatTwo.neg_branch_implies_kernel
#print axioms RevHalt.ArithNatTwo.S2prov_ssubset_S3TwoKit_of_frontier_nonempty
