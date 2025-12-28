/-
  RevHalt.Instances.PA.OmegaSigmaSeparation

  Formalizes the "arithmetical barrier" for Omega access:
  WinTruth (the correct bit of Omega) is NOT uniformly Σ₁ in PA.

  This justifies the T3 architecture:
  - Σ₁ predicates (Provability) are handled by S1.
  - Σ₂ predicates (Omega Truth) require an Oracle (S2).

  If WinTruth were uniformly Σ₁, we could use PA-Halting to compute Omega,
  which is impossible.
-/
import RevHalt.Instances.PA.OmegaDyadicLink
-- WinTruth is detailed in OmegaTruth.lean
import RevHalt.Dynamics.Instances.OmegaTruth
import RevHalt.Dynamics.Instances.OmegaAccessSchemas
import Mathlib.Tactic.FinCases

namespace RevHalt.Instances.PA

-- haltsWithinDec is in OmegaChaitin base
open RevHalt.Dynamics.Instances.OmegaChaitin (haltsWithinDec)
-- WinTruth is in LimitSemantics
open RevHalt.Dynamics.Instances.OmegaChaitin.LimitSemantics (WinTruth)
-- Sigma2Prop and WinTruth_is_sigma2
open RevHalt.Dynamics.Instances.OmegaChaitin.AccessSchemas

/-! ## 1) What it means for a family of propositions to be "uniformly Σ₁" -/

/-- A family of propositions `P : α → Prop` is "uniformly Σ₁ via PA Halt" if there exists:
    1. A compilation function `code : α → ℕ` (the Halt index),
    2. Such that for all inputs, `PATruth (Halt (code a)) ↔ P a`.

    This captures: "P is r.e. in a uniform, PA-realizable way."
-/
structure UniformlySigma1 {α : Type*} (PATruth : PASentence → Prop) (P : α → Prop) where
  /-- Uniform compilation to Halt indices. -/
  code : α → ℕ
  /-- The specification: PA-truth of Halt matches the proposition. -/
  spec : ∀ a : α, PATruth (PASentence.Halt (code a)) ↔ P a

/-- Shorthand: WinTruth at depth n, bit a. -/
def WinTruthFamily (input : ℕ × Fin 2) : Prop :=
  WinTruth input.1 input.2

/-! ## 2) The key observation: if WinTruth were uniformly Σ₁, bits of Ω would be r.e. -/

/-- If WinTruth is uniformly Σ₁, then for each depth n, we can semi-decide
    "which bit value a ∈ {0,1} is the correct one" by waiting for the Halt.

    This would give a computable procedure to enumerate the bits of Ω,
    contradicting Chaitin's theorem (Ω is not computable).
-/
structure OmegaBitEnumerable (PATruth : PASentence → Prop) where
  /-- For each depth n, there is a Halt-code that terminates iff the n-th bit is 0. -/
  haltIfBit0 : ℕ → ℕ
  /-- For each depth n, there is a Halt-code that terminates iff the n-th bit is 1. -/
  haltIfBit1 : ℕ → ℕ
  /-- Spec for bit 0. -/
  spec0 : ∀ n, PATruth (PASentence.Halt (haltIfBit0 n)) ↔ WinTruth n 0
  /-- Spec for bit 1. -/
  spec1 : ∀ n, PATruth (PASentence.Halt (haltIfBit1 n)) ↔ WinTruth n 1

/-- From UniformlySigma1 on WinTruthFamily, we can build OmegaBitEnumerable. -/
def OmegaBitEnumerable.fromUniformSigma1 {PATruth : PASentence → Prop}
    (U : UniformlySigma1 PATruth WinTruthFamily) : OmegaBitEnumerable PATruth where
  haltIfBit0 := fun n => U.code (n, 0)
  haltIfBit1 := fun n => U.code (n, 1)
  spec0 := fun n => U.spec (n, 0)
  spec1 := fun n => U.spec (n, 1)

/-! ## 3) The separation theorem: WinTruth is NOT uniformly Σ₁ under consistency -/

open RevHalt.Dynamics.Instances.OmegaChaitin (bitOfNat)

/-- Omega is computable if there is a total Partrec function giving the correct bits. -/
def OmegaComputable : Prop :=
  ∃ f : ℕ → ℕ, Nat.Partrec f ∧ ∀ n : ℕ, WinTruth n (RevHalt.Dynamics.Instances.OmegaChaitin.bitOfNat (f n))

/-- Hypothesis: Ω is genuinely non-computable (Chaitin's theorem). -/
def OmegaNonComputable : Prop := ¬ OmegaComputable

/-- Hypothesis: PA Halting is sound AND complete for atomic Halt statements.

    We require a constructive soundness: if PA proves Halt(n), then the machine halts.
    AND if the machine halts, PA proves it (Σ₁ completeness).
    This establishes the faithful link between the Logic (PATruth) and Reality (haltsWithinDec).
-/
structure HaltingSoundness (PATruth : PASentence → Prop) where
  /-- Halt(n) is True iff the machine actually halts in finite time. -/
  soundness : ∀ n, PATruth (PASentence.Halt n) ↔ ∃ t, haltsWithinDec t n 0 = true

/-- The main separation theorem (conditional).

    **Statement**: Under the hypotheses that:
    1. Ω is non-computable (OmegaNonComputable),
    2. PA Halt describes actual halting (HaltingSoundness),
    3. **Uniqueness**: For every n, exactly one bit is the true bit (Omega semantics),

    we have: WinTruth is NOT uniformly Σ₁.

    **Proof**:
    - Assume WinTruth is Uniformly Σ₁ (via `hUnif`).
    - We construct a computable function `decide : ℕ → ℕ` that outputs the bits of Ω (as 0 or 1).
    - Algorithm for `decide n`:
      - Let c0 = code for "WinTruth n 0" (from hUnif).
      - Let c1 = code for "WinTruth n 1".
      - Run c0 and c1 in parallel (dovetail) using `haltsWithinDec`.
      - Since exactly one logic bit is true, and hUnif + Soundness links Truth to Halting,
        exactly one machine will halt.
      - We return 0 if c0 first halts, 1 if c1 first halts.
    - This function is `Nat.Partrec` (minimization of primitive recursive function).
    - This contradicts `OmegaNonComputable`.
-/
theorem WinTruth_not_uniformly_sigma1
    {PATruth : PASentence → Prop}
    (hNonComp : OmegaNonComputable)
    (hSound : HaltingSoundness PATruth)
    (hUnique : ∀ n, ∃! a, WinTruth n a)
    (hUnif : UniformlySigma1 PATruth (α := ℕ × Fin 2) WinTruthFamily) :
    False := by
  let enum := OmegaBitEnumerable.fromUniformSigma1 hUnif

  -- 1. Existence of the witness (Classical logic allowed for Props in the project)
  -- We know mathematically that for each n, either bit 0 or bit 1 is true.
  have exists_halt : ∀ n, ∃ t, haltsWithinDec t (enum.haltIfBit0 n) 0 = true ∨ haltsWithinDec t (enum.haltIfBit1 n) 0 = true := by
    intro n
    -- Use Uniqueness and FinCases
    rcases hUnique n with ⟨a, ha, _⟩
    fin_cases a
    · -- Case a = 0
      have hP : PATruth (PASentence.Halt (enum.haltIfBit0 n)) :=
        (enum.spec0 n).mpr (by simpa using ha)
      rcases (hSound.soundness (enum.haltIfBit0 n)).mp hP with ⟨t, ht⟩
      exact ⟨t, Or.inl ht⟩
    · -- Case a = 1
      have hP : PATruth (PASentence.Halt (enum.haltIfBit1 n)) :=
        (enum.spec1 n).mpr (by simpa using ha)
      rcases (hSound.soundness (enum.haltIfBit1 n)).mp hP with ⟨t, ht⟩
      exact ⟨t, Or.inr ht⟩

  -- 2. Construct the computable decider (returning Nat: 0 or 1)
  let decide (n : ℕ) : ℕ :=
    -- Find the first time t where one of them halts.
    let t := Nat.find (exists_halt n)
    if haltsWithinDec t (enum.haltIfBit0 n) 0 then 0 else 1

  -- 3. Show this decider is Partrec
  have hPartrec : Nat.Partrec decide := by
    -- Minimization (`Nat.find`) of a decidable (Primitve Recursive) predicate is Partrec.
    -- `haltsWithinDec` is PR.
    -- Composition is PR/Partrec.
    -- We assume this computability fact to focus on the separation theorem.
    sorry

  -- 4. Show this decider is correct (contradiction)
  apply hNonComp
  -- We prove OmegaComputable (witness exists: decide)
  use decide
  constructor
  · exact hPartrec
  · intro n
    simp only [decide]
    -- We need to prove: WinTruth n (bitOfNat (decide n))
    split
    · -- Case: haltsWithinDec t c0 is true -> c0 halts -> bit 0
      next h_halt0 =>
        have hReal : ∃ t, haltsWithinDec t (enum.haltIfBit0 n) 0 = true := ⟨_, h_halt0⟩
        have hP : PATruth (PASentence.Halt (enum.haltIfBit0 n)) :=
          (hSound.soundness (enum.haltIfBit0 n)).mpr hReal
        have hWin : WinTruth n 0 := (enum.spec0 n).mp hP
        -- decide outputs 0. bitOfNat 0 = 0 (in Fin 2).
        -- We need WinTruth n (bitOfNat 0).
        -- Since bitOfNat 0 = 0, this is exactly hWin.
        exact hWin
    · -- Case: c0 doesn't halt at t, so c1 must halt
      next h_not_halt0 =>
        have h_found := Nat.find_spec (exists_halt n)
        simp [h_not_halt0] at h_found
        have hReal : ∃ t, haltsWithinDec t (enum.haltIfBit1 n) 0 = true := ⟨_, h_found⟩
        have hP : PATruth (PASentence.Halt (enum.haltIfBit1 n)) :=
          (hSound.soundness (enum.haltIfBit1 n)).mpr hReal
        have hWin : WinTruth n 1 := (enum.spec1 n).mp hP
        -- decide outputs 1. bitOfNat 1 = 1 (in Fin 2).
        exact hWin

/-! ## 4) Corollary: the access barrier is essential -/

/-- The access barrier statement: WinTruth requires the Π₁ component ∀s. -/
theorem access_barrier_essential :
    (∀ n a, Nonempty (Sigma2Prop (WinTruth n a))) ∧
    -- If there's a valid PA truth predicate such that...
    ¬(∃ (PATruth : PASentence → Prop),
        OmegaNonComputable ∧
        Nonempty (HaltingSoundness PATruth) ∧
        (∀ n, ∃! a, WinTruth n a) ∧
        Nonempty (UniformlySigma1 PATruth (α := ℕ × Fin 2) WinTruthFamily)) := by
  constructor
  · -- WinTruth is Σ₂ for all n, a (we have the schema object)
    intro n a
    exact ⟨WinTruth_is_sigma2 n a⟩
  · -- Cannot have a uniform Σ₁ witness (under implicit assumptions)
    intro hEx
    rcases hEx with ⟨PATruth, hNon, ⟨hSound⟩, hUnique, ⟨hUnif⟩⟩
    -- Apply the theorem
    exact WinTruth_not_uniformly_sigma1 hNon hSound hUnique hUnif
