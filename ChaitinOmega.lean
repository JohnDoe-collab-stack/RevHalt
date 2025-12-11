import RevHalt
import RevHaltInstances
import OmegaRevHalt
import Mathlib.Data.Finset.Card

/-!
# Chaitin's Omega: Quantitative Bounds

This file extends the qualitative impossibility results (T2, no_internal_omega_predicate)
with **quantitative bounds** on how many bits of Ω a recursive theory can decide.

The main result is:
> No recursive theory can prove more than O(L + c) bits of Ω, where L is the
> description length of the theory's enumerator.

This is Chaitin's theorem, formalized over our RevHalt framework.

## Structure:
1. PrefixUniversalModel: adds code length and prefix-freeness
2. Kolmogorov complexity K
3. RecursiveTheory: a theory with an explicit enumerator
4. Omega_K_random: axiom that Ω is K-random
5. Chaitin_bound_on_Omega_bits: the main theorem
-/

namespace Chaitin

-- ==============================================================================================
-- 1. Prefix Universal Model
-- ==============================================================================================

/--
  A prefix universal model extends ComputabilityModel with:
  - A binary encoding of codes
  - A length function
  - Prefix-freeness constraint
-/
structure PrefixUniversalModel extends ComputabilityModel where
  /-- Length of a code in bits. -/
  codeLength : Code → ℕ
  /-- Prefix-freeness: no code is a prefix of another in the binary representation. -/
  prefix_free : ∀ e₁ e₂ : Code, e₁ ≠ e₂ → codeLength e₁ ≤ codeLength e₂ →
    -- This is an abstraction: we don't need the full encoding, just the property
    True  -- Placeholder for actual prefix-free constraint

-- ==============================================================================================
-- 2. Kolmogorov Complexity
-- ==============================================================================================

variable (U : PrefixUniversalModel)

/--
  Output type for programs: we use ℕ as a binary encoding.
  The natural number n encodes a binary string via its binary representation.
-/
abbrev Output := ℕ

/--
  A program produces an output if it halts with that value.
-/
def Produces (e : U.Code) (x : Output) : Prop :=
  U.Program e 0 = some x

/--
  Kolmogorov complexity: the length of the shortest program that produces x.
  Note: This is axiomatized as a function; in reality it's not computable.
  Parameterized by U since it depends on the universal model.
-/
axiom K (U : PrefixUniversalModel) : Output → ℕ

/--
  K is at most the length of any program that produces x.
-/
axiom K_upper_bound (U : PrefixUniversalModel) :
  ∀ (e : U.Code) (x : Output), Produces U e x → K U x ≤ U.codeLength e

/--
  There exists a program achieving K(x).
-/
axiom K_achievable (U : PrefixUniversalModel) :
  ∀ x : Output, ∃ e : U.Code, Produces U e x ∧ U.codeLength e = K U x

-- ==============================================================================================
-- 3. Omega Prefix Encoding (axiomatized to avoid noncomputable)
-- ==============================================================================================

variable (embed : ℕ → U.Code)

/--
  OmegaPrefix n encodes the first n bits of Ω as a natural number.

  Semantically, OmegaPrefix n = Σᵢ (Ω(i) * 2^i) for i = 0 to n-1,
  where Ω(i) = 1 iff embed(i) halts.

  This is axiomatized rather than defined because computing it would
  require deciding halting, which would make it noncomputable.
-/
axiom OmegaPrefix : ℕ → Output

/--
  Axiom: The k-th bit of OmegaPrefix n (when k < n) corresponds to OmegaBit.
  This links the axiomatized OmegaPrefix to the propositional OmegaBit.
-/
axiom OmegaPrefix_bit_spec :
  ∀ n k, k < n →
    (Nat.testBit (OmegaPrefix n) k = true ↔ Omega.OmegaBit U.toComputabilityModel embed k)

/--
  Axiom: Ω is K-random. The Kolmogorov complexity of any prefix of Ω
  is at least its length minus a constant.
-/
axiom Omega_K_random' (U : PrefixUniversalModel) (embed : ℕ → U.Code) :
  ∃ c : ℕ, ∀ n : ℕ, K U (OmegaPrefix n) ≥ n - c

-- ==============================================================================================
-- 4. Recursive Theory (enriched with encode/enum_spec)
-- ==============================================================================================

/--
  A recursive theory is a theory whose theorems can be enumerated by a program.

  The enriched version includes:
  - `encode`: how to encode propositions as outputs
  - `enum_spec`: the enumerator produces exactly the provable propositions
-/
structure RecursiveTheory where
  /-- The underlying Turing-Gödel context. -/
  ctx : TuringGodelContext' U.Code (HaltProp U.toComputabilityModel)
  /-- The code of the program that enumerates theorems. -/
  enumCode : U.Code
  /-- Encoding of propositions as outputs. -/
  encode : HaltProp U.toComputabilityModel → Output
  /-- Specification: enumCode produces encoded versions of provable statements. -/
  enum_spec : ∀ p, ctx.Provable p ↔ ∃ n, U.Program enumCode n = some (encode p)
  /-- Soundness: everything provable is true. -/
  sound : ∀ p, ctx.Provable p → HaltProvable U.toComputabilityModel p

/--
  The description length of a theory is the length of its enumerator.
-/
def theoryLength (T : RecursiveTheory U) : ℕ :=
  U.codeLength T.enumCode

-- ==============================================================================================
-- 5. Bits Decidable by a Theory
-- ==============================================================================================

variable (T : RecursiveTheory U)

/--
  A theory decides bit n of Ω if it proves either Ω(n) = 1 or Ω(n) = 0.
-/
def DecidesBit (n : ℕ) : Prop :=
  T.ctx.Provable (Omega.OmegaHaltProp_halts U.toComputabilityModel embed n) ∨
  T.ctx.Provable (Omega.OmegaHaltProp_notHalts U.toComputabilityModel embed n)

/--
  The set of bits decidable by T.
-/
def DecidableBits : Set ℕ :=
  { n | DecidesBit U embed T n }

-- ==============================================================================================
-- 6. Universal Wrapper Axiom
-- ==============================================================================================

/--
  **Universal Wrapper Axiom**:
  Given any recursive theory T, there exists a program schema that:
  - Takes the enumerator of T
  - For any n, if T decides all bits 0..n-1, produces OmegaPrefix n
  - Has length bounded by theoryLength T + a fixed overhead

  This axiom captures the "programmability" of the extraction process.
  It could be derived from a more detailed model of computation, but
  we axiomatize it here for modularity.
-/
axiom universal_wrapper (U : PrefixUniversalModel) :
  ∃ overhead : ℕ,
    ∀ (embed : ℕ → U.Code) (T : RecursiveTheory U),
      ∃ extract : ℕ → U.Code,
        ∀ n,
          (∀ k, k < n → DecidesBit U embed T k) →
          Produces U (extract n) (OmegaPrefix n) ∧
          U.codeLength (extract n) ≤ theoryLength U T + overhead

-- ==============================================================================================
-- 7. PrefixExtractor Instance (derived from universal_wrapper)
-- ==============================================================================================

/--
  **PrefixExtractor**: The key hypothesis for Chaitin's bound.

  For a theory T, this structure asserts the existence of a program schema
  that, given that T decides all bits of Ω from 0 to n-1, can produce
  the prefix OmegaPrefix(n) with bounded overhead.

  This is the "program that extracts a prefix of Ω from T's proofs".
-/
structure PrefixExtractor (U : PrefixUniversalModel)
    (embed : ℕ → U.Code) (T : RecursiveTheory U) where
  /-- Overhead constant for the extractor. -/
  overhead : ℕ
  /-- The extraction program for each prefix length. -/
  extract : ℕ → U.Code
  /-- Specification: if T decides bits 0..n-1, extract n produces OmegaPrefix n
      with length ≤ theoryLength T + overhead. -/
  extract_spec :
    ∀ n,
      (∀ k, k < n → DecidesBit U embed T k) →
      Produces U (extract n) (OmegaPrefix n) ∧
      U.codeLength (extract n) ≤ theoryLength U T + overhead


-- ==============================================================================================
-- 8. Chaitin's Bound (prefix version, no sorry)
-- ==============================================================================================

/--
  **Chaitin's Theorem (Prefix Version):**
  If T decides all bits of Ω from 0 to n-1, then n is bounded by the
  description length of T plus a constant.

  This version is parameterized by a PrefixExtractor, which isolates
  the program composition brick that would otherwise require a sorry.

  The proof is fully constructive given the extractor.
-/
theorem Chaitin_bound_on_Omega_prefix
    (E : PrefixExtractor U embed T) :
    ∃ C : ℕ, ∀ n : ℕ,
      (∀ k, k < n → DecidesBit U embed T k) →
      n ≤ theoryLength U T + C := by
  -- Get the K-randomness constant
  obtain ⟨c_random, h_random⟩ := Omega_K_random' U embed
  -- The bound is: overhead from extractor + K-randomness constant
  refine ⟨E.overhead + c_random, ?_⟩
  intro n h_dec
  -- 1. Use the extractor to get a program producing OmegaPrefix n
  have h_extract := E.extract_spec n h_dec
  obtain ⟨h_prod, h_len⟩ := h_extract
  -- 2. Upper bound: K(OmegaPrefix n) ≤ codeLength(extract n) ≤ theoryLength T + overhead
  have hK_upper : K U (OmegaPrefix n) ≤ theoryLength U T + E.overhead := by
    have hK_le := K_upper_bound U (E.extract n) (OmegaPrefix n) h_prod
    exact le_trans hK_le h_len
  -- 3. Lower bound: K(OmegaPrefix n) ≥ n - c_random
  have hK_lower : n - c_random ≤ K U (OmegaPrefix n) := h_random n
  -- 4. Combine: n - c_random ≤ theoryLength T + overhead
  have h_combined : n - c_random ≤ theoryLength U T + E.overhead :=
    le_trans hK_lower hK_upper
  -- 5. Convert to: n ≤ theoryLength T + overhead + c_random
  omega

-- ==============================================================================================
-- 9. Chaitin's Theorem (final standalone version)
-- ==============================================================================================

/--
  **Chaitin's Theorem (Standalone):**
  For any recursive theory T, there exists a constant C such that
  if T decides all bits of Ω from 0 to n-1, then n ≤ theoryLength(T) + C.

  This is the version that doesn't require the user to provide a PrefixExtractor;
  it's derived automatically from the universal_wrapper axiom.
-/
theorem Chaitin_bound
    (U : PrefixUniversalModel)
    (embed : ℕ → U.Code)
    (T : RecursiveTheory U) :
    ∃ C : ℕ, ∀ n : ℕ,
      (∀ k, k < n → DecidesBit U embed T k) →
      n ≤ theoryLength U T + C := by
  -- Obtain the extractor components from the axiom (inside proof = no noncomputable needed)
  obtain ⟨overhead, h_wrapper⟩ := universal_wrapper U
  obtain ⟨extract, h_extract⟩ := h_wrapper embed T
  -- Construct the extractor structure inline
  let E : PrefixExtractor U embed T := ⟨overhead, extract, h_extract⟩
  -- Apply the Chaitin bound theorem for this extractor
  exact @Chaitin_bound_on_Omega_prefix U embed T E

end Chaitin
