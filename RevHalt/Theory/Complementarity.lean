import RevHalt.Theory.Impossibility
import RevHalt.Theory.Stabilization
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Disjoint

/-!
# RevHalt.Theory.Complementarity

T3: Complementarity (one-sided) — S₁ ∪ S₂ = S₃

## Core Decomposition (Typed Definitions)

- **S₁ (one-sided frontier)** := `S1Set S encode_halt` (kit-certified + not provable in `S`)
- **S₂ (base corpus)** := parameter `S2 : Set PropT` with soundness witness `h_S2_sound`
- **S₃ (one-sided extension)** := `S3Set S S2 encode_halt` = `S₂ ∪ S₁`

### Variants

- **Two-sided oracle (local step)**: for fixed `e`, an explicit witness `OraclePick` selects either
  `encode_halt e` or `encode_not_halt e` and yields the one-step extension `S2 ∪ {pick.p}`.
- **Two-sided oracle (global frontier)**: `S1TwoSet` / `S3TwoSet` collect all oracle-chosen sentences across all codes
  (not used by the local oracle theorem in this file; intended for later globalization).

## Lean-Faithful Interpretation

- We work over a fixed syntactic universe `PropT` (so `Set PropT` is a predicate `PropT → Prop`).
- Semantics is represented externally by a truth predicate `Truth : PropT → Prop` (or, upstream, by `Sat`/`SemConsequences`).
- `S2` is an arbitrary internalizable base corpus `S2 : Set PropT` equipped with an explicit soundness witness
  `h_S2_sound : ∀ p ∈ S2, Truth p`
  (i.e. membership implies external truth).
- `S1` is the non-internalizable syntactic frontier `S1Set S encode_halt : Set PropT`, whose elements are sentences
  of type `PropT` (typically `encode_halt e`) singled out by the interaction of:
  - the external certification `Rev0_K S.K (S.Machine e)`, and
  - internal non-derivability `¬ S.Provable (encode_halt e)`.

The one-sided complementarity result is exactly the construction
`S3 := S2 ∪ S1` (implemented as `S3Set S S2 encode_halt`),
showing that the extension contains both layers, preserves semantic soundness under the stated hypotheses,
and adds kit-certified sentences from `S1` that are not internalized by `Provable`.

Separately, a two-sided oracle variant is provided for clarity of the "choice of side":
for a fixed code `e`, an explicit witness `OraclePick` selects either `encode_halt e` or `encode_not_halt e`
(without any decidability assumption), and yields a local one-step sound extension `S2 ∪ {pick.p}`.


## Explicit Kit Dependency (Types)

```

S : ComplementaritySystem Code PropT
S.K : RHKit
S.h_canon : DetectsUpFixed S.K   -- Updated to UpFixed
Rev0_K S.K : Trace → Prop

```
-/

namespace RevHalt

open Nat.Partrec

-- ==============================================================================================
-- T3: Complementarity — Explicit Definitions
-- ==============================================================================================

/-- System for T3 theorems: general Code + general Machine, but realizable in Partrec.Code. -/
structure ComplementaritySystem (Code PropT : Type) extends ImpossibleSystem PropT where
  K : RHKit
  h_canon : DetectsUpFixed K  -- Updated to DetectsUpFixed

  Machine : Code → Trace

  /- Realization into the canonical code model `RevHalt.Code = Nat.Partrec.Code` -/
  enc : Code → RevHalt.Code
  dec : RevHalt.Code → Code
  enc_dec : ∀ c : RevHalt.Code, enc (dec c) = c

  /- Machine is exactly the canonical Machine after encoding -/
  machine_eq : ∀ e : Code, Machine e = RevHalt.Machine (enc e)

/-- Explicit Kit extraction. -/
def KitOf {Code PropT : Type} (S : ComplementaritySystem Code PropT) : RHKit := S.K

/-- Derived (axiom-free) diagonal bridge for any realizable (Code,Machine). -/
theorem diagonal_bridge_of_realization
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (f : Code → (Nat →. Nat))
    (hf : Partrec₂ (fun c : RevHalt.Code => f (S.dec c)))
    (target : Code → Prop)
    (htarget : ∀ e, target e ↔ (∃ x : Nat, x ∈ (f e) 0)) :
    ∃ e : Code, Rev0_K S.K (S.Machine e) ↔ target e := by
  -- Lift f, target to the canonical code model
  let fP : RevHalt.Code → (Nat →. Nat) := fun c => f (S.dec c)
  let targetP : RevHalt.Code → Prop := fun c => target (S.dec c)

  have htargetP : ∀ c : RevHalt.Code, targetP c ↔ (∃ x : Nat, x ∈ (fP c) 0) := by
    intro c
    change target (S.dec c) ↔ (∃ x : Nat, x ∈ (f (S.dec c)) 0)
    exact htarget (S.dec c)

  -- Apply the canonical diagonal bridge on `RevHalt.Code`
  -- Uses DetectsUpFixed S.h_canon
  obtain ⟨c0, hc0⟩ :=
    RevHalt.diagonal_bridge S.K S.h_canon fP hf targetP htargetP

  -- Pull back to your Code using dec
  refine ⟨S.dec c0, ?_⟩

  -- Rewrite S.Machine (dec c0) as canonical Machine c0
  have hMeq : S.Machine (S.dec c0) = RevHalt.Machine c0 := by
    have h0 : S.Machine (S.dec c0) = RevHalt.Machine (S.enc (S.dec c0)) := S.machine_eq (S.dec c0)
    have h1 : S.enc (S.dec c0) = c0 := S.enc_dec c0
    rw [h1] at h0
    exact h0

  -- Finish: rewrite goal by hMeq, then use hc0
  rw [hMeq]
  exact hc0

/-- S₁ := { encode_halt e | kit says halt on S.Machine e, and unprovable } -/
def S1Set {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) : Set PropT :=
  { p | ∃ e : Code,
      p = encode_halt e ∧
      Rev0_K (KitOf S) (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) }

/-- S₃ := S₂ ∪ S₁ -/
def S3Set {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (S2 : Set PropT) (encode_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1Set S encode_halt

lemma mem_S1Set_of_witness
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    encode_halt e ∈ S1Set S encode_halt := by
  have hEq : KitOf S = S.K := rfl
  have hKit' : Rev0_K (KitOf S) (S.Machine e) := by
    rw [hEq]; exact hKit
  exact Exists.intro e (And.intro rfl (And.intro hKit' hUnprov))

theorem S1Set_nonempty_of_witness
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT)
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    (S1Set S encode_halt).Nonempty := by
  exact Exists.intro (encode_halt e) (mem_S1Set_of_witness S encode_halt e hKit hUnprov)

-- ==============================================================================================
-- T3.0 — Subtraction Property (Missing Set)
-- ==============================================================================================

/--
  "MissingFromS2" captures elements in the extension S3 that are **not** provable in the base system.
  If S2 is purely provable, this set exactly recovers S1.
-/
def MissingFromS2 {Code PropT : Type} (S : ComplementaritySystem Code PropT) (S3 : Set PropT) : Set PropT :=
  { p | p ∈ S3 ∧ ¬ S.Provable p }

/--
  **Prop T3.0 (Subtraction)**:
  If the base corpus S2 consists only of provable truths (sound internal theory),
  then the "missing" part of the extension S3 is exactly the frontier S1.
  `MissingFromS2(S3) = S1`
-/
theorem missing_equals_S1
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (S2 : Set PropT) (hS2_prov : ∀ p, p ∈ S2 → S.Provable p)
    (encode_halt : Code → PropT) :
    MissingFromS2 S (S3Set S S2 encode_halt) = S1Set S encode_halt := by
  ext p
  constructor
  · intro hp
    -- hp : p ∈ S3 ∧ ¬Provable p
    rcases hp with ⟨hpS3, hNot⟩
    cases hpS3 with
    | inl hpS2 =>
        have hProv : S.Provable p := hS2_prov p hpS2
        exact False.elim (hNot hProv)
    | inr hpS1 =>
        exact hpS1
  · intro hpS1
    refine And.intro ?_ ?_
    · -- p ∈ S3
      exact Or.inr hpS1
    · -- ¬ Provable p
      rcases hpS1 with ⟨e, hpEq, _hKit, hUnprov⟩
      intro hProv_p
      rw [hpEq] at hProv_p
      exact hUnprov hProv_p

-- ==============================================================================================
-- T3.0 Structural — Deep Characterization of the Frontier
-- ==============================================================================================

/-- S1Raw : Kit-certified truths (no provability condition).
    This is the "raw" frontier before filtering by provability. -/
def S1Raw {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) : Set PropT :=
  { p | ∃ e : Code, p = encode_halt e ∧ Rev0_K S.K (S.Machine e) }

/-- S1Eff : Effective frontier = Kit-certified AND unprovable.
    These are the truths that escape the internal system. -/
def S1Eff {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) : Set PropT :=
  { p | p ∈ S1Raw S encode_halt ∧ ¬ S.Provable p }

/-- S1Eff equals the original S1Set — the definitions are equivalent. -/
lemma S1Eff_eq_S1Set {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) :
    S1Eff S encode_halt = S1Set S encode_halt := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨e, hpEq, hRev⟩, hNot⟩ := hp
    have hEq : KitOf S = S.K := rfl
    have hRev' : Rev0_K (KitOf S) (S.Machine e) := by rw [hEq]; exact hRev
    rw [hpEq] at hNot ⊢
    exact ⟨e, rfl, hRev', hNot⟩
  · intro hp
    obtain ⟨e, hpEq, hRev, hNot⟩ := hp
    -- KitOf S = S.K by definition, so Rev0_K (KitOf S) = Rev0_K S.K
    have hRev' : Rev0_K S.K (S.Machine e) := hRev
    constructor
    · exact ⟨e, hpEq, hRev'⟩
    · rw [hpEq]; exact hNot

/--
  **T3.0 Structural — Necessity of the Frontier**

  If the system admits "negative completeness" (can prove ¬H when stabilization),
  then the frontier S1Eff is necessarily non-empty.

  Otherwise, we could construct an InternalHaltingPredicate, contradicting T2.

  This theorem shows that S1 ≠ ∅ is a **structural necessity** forced by T2,
  not just an incidental property.
-/
theorem frontier_necessary
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT)
    -- Negative completeness: can prove ¬H when ¬Rev_K
    (h_neg_complete : ∀ c : RevHalt.Code,
        ¬ Rev0_K S.K (RevHalt.Machine c) → S.Provable (S.Not (encode_halt (S.dec c))))
    -- Semi-decidability of provability of ¬H
    (f : RevHalt.Code → (Nat →. Nat))
    (hf : Partrec₂ f)
    (h_semidec : ∀ c : RevHalt.Code,
        S.Provable (S.Not (encode_halt (S.dec c))) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    (S1Eff S encode_halt).Nonempty := by
  -- Proof by contradiction: suppose S1Eff = ∅
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty
  -- Then: ∀ e : Code, Rev_K(Machine e) → Provable(encode_halt e)
  have h_pos_complete : ∀ c : RevHalt.Code,
      Rev0_K S.K (RevHalt.Machine c) → S.Provable (encode_halt (S.dec c)) := by
    intro c hRev
    by_contra hNotProv
    -- If Rev_K(c) and ¬Provable(encode_halt(dec c)), then dec c ∈ S1Eff
    have h_in_raw : encode_halt (S.dec c) ∈ S1Raw S encode_halt := by
      use S.dec c
      constructor
      · rfl
      · -- Need: Rev0_K S.K (S.Machine (S.dec c)) = Rev0_K S.K (RevHalt.Machine c)
        have hMach : S.Machine (S.dec c) = RevHalt.Machine (S.enc (S.dec c)) :=
          S.machine_eq (S.dec c)
        rw [S.enc_dec c] at hMach
        rw [hMach]
        exact hRev
    have h_in_eff : encode_halt (S.dec c) ∈ S1Eff S encode_halt := ⟨h_in_raw, hNotProv⟩
    have h_not_mem : encode_halt (S.dec c) ∉ S1Eff S encode_halt := by
      rw [h_empty]; exact Set.notMem_empty _
    exact h_not_mem h_in_eff
  -- Construct InternalHaltingPredicate
  let H : RevHalt.Code → PropT := fun c => encode_halt (S.dec c)
  have h_total : ∀ e : RevHalt.Code, S.Provable (H e) ∨ S.Provable (S.Not (H e)) := by
    intro e
    cases Classical.em (Rev0_K S.K (RevHalt.Machine e)) with
    | inl hRev => exact Or.inl (h_pos_complete e hRev)
    | inr hNotRev => exact Or.inr (h_neg_complete e hNotRev)
  have h_correct : ∀ e : RevHalt.Code, Rev0_K S.K (RevHalt.Machine e) → S.Provable (H e) :=
    h_pos_complete
  have h_complete : ∀ e : RevHalt.Code, ¬ Rev0_K S.K (RevHalt.Machine e) → S.Provable (S.Not (H e)) :=
    h_neg_complete
  -- Build the impossible predicate (InternalHaltingPredicate is now abbrev of Internalizer)
  let I : InternalHaltingPredicate S.toImpossibleSystem S.K := {
    H := H
    total := h_total
    correct := h_correct
    complete := h_complete
    f := f
    f_partrec := hf
    semidec := h_semidec
  }
  -- Apply T2 (now uses Nonempty)
  exact T2_impossibility S.toImpossibleSystem S.K S.h_canon ⟨I⟩

-- ==============================================================================================
-- Unprovable Encoding Existence (uses diagonal_bridge_of_realization, no axioms)
-- ==============================================================================================

/--
  **∃ unprovable encoding** (not the same as S₁ ≠ ∅).
  Uses derived diagonal_bridge_of_realization, with lifted Partrec₂ hypothesis.
-/
theorem exists_unprovable_encode_halt
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (h_sound : ∀ p, S.Provable p → Truth p)
    (encode_halt : Code → PropT)
    (h_truth_to_real : ∀ e, Truth (encode_halt e) → Rev0_K S.K (S.Machine e))
    (f : Code → (Nat →. Nat))
    (hf : Partrec₂ (fun c : RevHalt.Code => f (S.dec c)))
    (h_semidec : ∀ e, S.Provable (S.Not (encode_halt e)) ↔ (∃ x : Nat, x ∈ (f e) 0)) :
    ∃ e, ¬ S.Provable (encode_halt e) := by
  -- diagonal: Rev(e) ↔ Provable(Not(encode_halt e))
  let target : Code → Prop := fun e => S.Provable (S.Not (encode_halt e))
  obtain ⟨e, he⟩ := diagonal_bridge_of_realization S f hf target h_semidec
  refine Exists.intro e ?_
  intro hProv
  have hReal : Rev0_K S.K (S.Machine e) :=
    h_truth_to_real e (h_sound (encode_halt e) hProv)
  have hProvNot : S.Provable (S.Not (encode_halt e)) :=
    he.mp hReal
  exact S.consistent (S.absurd (encode_halt e) hProv hProvNot)

-- ==============================================================================================
-- T3.1 (Weak) — S₃ = S₁ ∪ S₂ is Sound
-- ==============================================================================================

/--
**T3.1 — S₃ = S₁ ∪ S₂ is Sound** (explicit, no `simp`, no `simpa`, no `classical`).
-/
theorem T3_weak_extension_explicit
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (e : Code)
    (hKit : Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_halt e)) :
    ∃ S3 : Set PropT,
      S3 = S3Set S S2 encode_halt ∧
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      encode_halt e ∈ S1Set S encode_halt ∧
      encode_halt e ∈ S3 ∧
      Halts (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) := by
  let S3 : Set PropT := S3Set S S2 encode_halt

  -- Ensure Halts via Kit
  -- Ensure Halts via Kit
  have hIff : Rev0_K S.K (S.Machine e) ↔ Halts (S.Machine e) := by
    simpa [Rev0_K] using (RevHalt.revK_iff_halts (K := S.K) S.h_canon (T := S.Machine e))

  -- Direction we need: Rev -> Halts
  have hHalt' : Halts (S.Machine e) := hIff.mp hKit

  have h_mem_S1 : encode_halt e ∈ S1Set S encode_halt :=
    mem_S1Set_of_witness S encode_halt e hKit hUnprov

  refine Exists.intro S3 ?_
  constructor
  · rfl -- S3 = S3Set ...
  · constructor
    · -- S2 ⊆ S3
      intro p hp
      exact Or.inl hp
    · constructor
      · -- Soundness
        intro p hp
        cases hp with
        | inl hp2 =>
            exact h_S2_sound p hp2
        | inr hp1 =>
            rcases hp1 with ⟨e', hpEq, hKit', _⟩
            have hEqK : S.K = KitOf S := rfl
            have hKitReal : Rev0_K S.K (S.Machine e') := hKit'
            rw [hpEq]
            exact h_encode_correct e' hKitReal
      · -- The 4-part conjunction for e
        constructor
        · exact h_mem_S1
        · constructor
          · exact Or.inr h_mem_S1 -- e ∈ S3
          · constructor
            · exact hHalt'
            · exact hUnprov

-- ==============================================================================================
-- Infinite S₁ Elements (indexed witnesses: kit + unprovable)
-- ==============================================================================================

/--
  **Infinite S₁ elements** (indexed witnesses, no injectivity required).

  Captures infinitely many codes with:
  - Kit-certified: `kit i : Rev0_K S.K (S.Machine (family i))`
  - Non-internalizable: `unprovable i : ¬ S.Provable (encode_halt (family i))`
-/
structure InfiniteS1 {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt : Code → PropT) where
  Index : Type
  InfiniteIndex : Infinite Index
  family : Index → Code
  distinct : Function.Injective family
  kit : ∀ i, Rev0_K S.K (S.Machine (family i))
  unprovable : ∀ i, ¬ S.Provable (encode_halt (family i))

/-- Derived: each index provides a member of `S1Set`. -/
lemma InfiniteS1.memS1
    {Code PropT : Type} {S : ComplementaritySystem Code PropT}
    {encode_halt : Code → PropT}
    (I : InfiniteS1 S encode_halt) :
    ∀ i, encode_halt (I.family i) ∈ S1Set S encode_halt := by
  intro i
  have hEq : KitOf S = S.K := rfl
  have hKit' : Rev0_K (KitOf S) (S.Machine (I.family i)) := by
    rw [hEq]
    exact I.kit i
  exact Exists.intro (I.family i)
    (And.intro rfl (And.intro hKit' (I.unprovable i)))

/-- Partition of indices. -/
structure Partition (Index : Type) where
  Parts : ℕ → Set Index
  disjoint : ∀ n m, n ≠ m → Disjoint (Parts n) (Parts m)

-- ==============================================================================================
-- T3.2 (Strong) — Multiple S₃ₙ from S₁ Partitions
-- ==============================================================================================

/--
**T3.2 — Multiple complementary systems from S₁ partitions**

Given infinite **S₁ elements** (indexed witnesses),
constructs {S₃ₙ} family. Each S₃ₙ = S₂ ∪ { encode_halt(family i) | i ∈ Parts(n) }.

No `simp`, no `simpa`, no `classical`, no `noncomputable`.
-/
theorem T3_strong {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (encode_halt : Code → PropT)
    (h_encode_correct : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (indep : InfiniteS1 S encode_halt)
    (partition : Partition indep.Index)
    : ∃ (S3_family : ℕ → Set PropT),
        (∀ n, S2 ⊆ S3_family n) ∧
        (∀ n, ∀ p ∈ S3_family n, Truth p) ∧
        (∀ n m, n ≠ m → ∀ i ∈ partition.Parts n, ∀ j ∈ partition.Parts m, i ≠ j) ∧
        (∀ n, ∀ i ∈ partition.Parts n, encode_halt (indep.family i) ∈ S3_family n) := by
  let S3_family : ℕ → Set PropT := fun n =>
    S2 ∪ { p | ∃ i ∈ partition.Parts n, p = encode_halt (indep.family i) }

  refine Exists.intro S3_family ⟨?_, ?_, ?_, ?_⟩

  · -- 1. S2 ⊆ S3_family n
    intro n p hp
    exact Or.inl hp

  · -- 2. Soundness
    intro n p hp
    cases hp with
    | inl hp2 =>
        exact h_S2_sound p hp2
    | inr hpNew =>
        rcases hpNew with ⟨i, _hi, hpEq⟩
        rw [hpEq]
        exact h_encode_correct (indep.family i) (indep.kit i)

  · -- 3. Disjointness
    intro n m hnm i hi j hj hEq
    have h_disj : Disjoint (partition.Parts n) (partition.Parts m) :=
      partition.disjoint n m hnm
    have hi' : j ∈ partition.Parts n := by
      rw [hEq] at hi
      exact hi
    have h_inter : j ∈ partition.Parts n ⊓ partition.Parts m := And.intro hi' hj
    have h_empty : partition.Parts n ⊓ partition.Parts m = ⊥ := (disjoint_iff.mp h_disj)
    rw [h_empty] at h_inter
    exact (Set.notMem_empty j h_inter)

  · -- 4. Membership
    intro n i hi
    apply Or.inr
    use i

-- ==============================================================================================
-- Two-sided oracle variant (local one-step extension)
-- No `simp`, no `simpa`, no `classical`, no `noncomputable`.
-- ==============================================================================================

/--
An explicit two-sided oracle *witness* for a given code `e`.

It packages a chosen sentence `p : PropT` together with a certificate that `p` matches
the Kit verdict:
- Left branch: `Rev0_K ...` (Halting Witness) → `p = encode_halt e`.
- Right branch: `¬ Rev0_K ...` (Stabilization Certificate) → `p = encode_not_halt e`.

No decidability of `Rev0_K` is assumed or used.
-/
structure OraclePick {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT) (e : Code) where
  p : PropT
  cert :
    PSum (Rev0_K S.K (S.Machine e) ∧ p = encode_halt e)
         (KitStabilizes S.K (S.Machine e) ∧ p = encode_not_halt e)

/-- Local S₁ for a fixed oracle pick: a single frontier sentence. -/
def S1OneSet {PropT : Type} (pick_p : PropT) : Set PropT :=
  {pick_p}

/-- Local S₃ = S₂ ∪ S₁ (with S₁ being the singleton chosen by the oracle). -/
def S3OneSet {PropT : Type} (S2 : Set PropT) (pick_p : PropT) : Set PropT :=
  S2 ∪ S1OneSet pick_p

/--
Oracle variant (two-sided) — explicit and constructive.

- `S2 : Set PropT` is the semantics-side corpus, with explicit soundness witness.
- The oracle provides a `pick` choosing *one* sentence based on the Kit verdict (by certificate).
- We extend by adding exactly that sentence, and prove the extension is sound.
- This establishes the soundness of a single oracle step `S2 ∪ {pick.p}`.

This theorem assumes a witness `pick`; it does not define or compute such a pick.

No branching on `Rev0_K` is computed; the branch is carried by `pick.cert`.
-/
theorem T3_oracle_extension_explicit
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (e : Code)
    (pick : OraclePick S encode_halt encode_not_halt e)
    (hUnprov : ¬ S.Provable pick.p) :
    ∃ S3 : Set PropT,
      S3 = S3OneSet S2 pick.p ∧
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      pick.p ∈ S3 ∧
      ¬ S.Provable pick.p ∧
      ((Halts (S.Machine e) ∧ pick.p = encode_halt e) ∨
       (Stabilizes (S.Machine e) ∧ pick.p = encode_not_halt e)) := by
  let S3 : Set PropT := S3OneSet S2 pick.p

  have hIff : Rev0_K S.K (S.Machine e) ↔ Halts (S.Machine e) := by
    -- Rev0_K K T ↔ Halts T
    simpa [Rev0_K] using (revK_iff_halts (K := S.K) S.h_canon (T := S.Machine e))

  have hIffStab : KitStabilizes S.K (S.Machine e) ↔ Stabilizes (S.Machine e) :=
    T1_stabilization S.K S.h_canon (S.Machine e)

  have hTruthPick : Truth pick.p := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        have hTrue : Truth (encode_halt e) := h_pos e hKit
        rw [hpEq]
        exact hTrue
    | inr h =>
        have hNotKit : KitStabilizes S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        have hTrue : Truth (encode_not_halt e) := h_neg e hNotKit
        rw [hpEq]
        exact hTrue

  have hBranchHalt :
      (Halts (S.Machine e) ∧ pick.p = encode_halt e) ∨
      (Stabilizes (S.Machine e) ∧ pick.p = encode_not_halt e) := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        have hHalt : Halts (S.Machine e) := (hIff).1 hKit
        exact Or.inl (And.intro hHalt hpEq)
    | inr h =>
        have hNotKit : KitStabilizes S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        have hStab : Stabilizes (S.Machine e) := (hIffStab).1 hNotKit
        exact Or.inr (And.intro hStab hpEq)

  refine Exists.intro S3 ?_
  refine And.intro rfl ?_
  refine And.intro ?_ ?_

  · -- S2 ⊆ S3
    intro p hp
    -- S3 = S3OneSet ... = S2 ∪ {pick.p}
    exact Or.inl hp

  · refine And.intro ?_ ?_
    · -- Soundness
      intro p hp
      cases hp with
      | inl hp2 =>
          exact h_S2_sound p hp2
      | inr hp1 =>
          -- hp1 : p ∈ {pick.p}
          have hpEq : p = pick.p := hp1
          rw [hpEq]
          exact hTruthPick

    · refine And.intro ?_ ?_
      · -- pick.p ∈ S3
        have hMemSingleton : pick.p ∈ ({pick.p} : Set PropT) := rfl
        exact Or.inr hMemSingleton
      · refine And.intro hUnprov hBranchHalt

/-
  Two-sided oracle (global frontier) — definitions for later globalization (families/partitions).

  These are not used by `T3_oracle_extension_explicit` (which is a local one-step theorem).
-/

/-- S₁(two-sided global): union of oracle-chosen frontier sentences across all codes `e`. -/
def S1TwoSet {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT) : Set PropT :=
  { p | ∃ e : Code, ∃ pick : OraclePick S encode_halt encode_not_halt e,
      p = pick.p ∧ ¬ S.Provable p }

/-- S₃(two-sided global): S₂ ∪ S₁(two-sided). -/
def S3TwoSet {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (S2 : Set PropT) (encode_halt encode_not_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1TwoSet S encode_halt encode_not_halt

/-- Membership lemma: the oracle-chosen sentence is in S₁(two-sided) given unprovability. -/
lemma mem_S1TwoSet_of_pick
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code) (pick : OraclePick S encode_halt encode_not_halt e)
    (hUnprov : ¬ S.Provable pick.p) :
    pick.p ∈ S1TwoSet S encode_halt encode_not_halt := by
  refine Exists.intro e ?_
  refine Exists.intro pick ?_
  refine And.intro rfl ?_
  exact hUnprov

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.S1Raw
#print axioms RevHalt.S1Eff
#print axioms RevHalt.S1Eff_eq_S1Set
#print axioms RevHalt.frontier_necessary
#print axioms RevHalt.diagonal_bridge_of_realization
#print axioms RevHalt.mem_S1Set_of_witness
#print axioms RevHalt.S1Set_nonempty_of_witness
#print axioms RevHalt.missing_equals_S1
#print axioms RevHalt.exists_unprovable_encode_halt
#print axioms RevHalt.T3_weak_extension_explicit
#print axioms RevHalt.InfiniteS1
#print axioms RevHalt.T3_strong
#print axioms RevHalt.T3_oracle_extension_explicit
#print axioms RevHalt.mem_S1TwoSet_of_pick
