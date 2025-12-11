import RevHalt
import RevHaltInstances

/-!
# Omega as a Cut of H*

This file formalizes Chaitin's Ω as a **cut** of the canonical halting predicate H*.

Key insight: Ω is not a mysterious external object — it is a sequence where
each bit is exactly an instance of RealHalts on a particular code.

This connects Ω directly to T2 (impossibility) and T3 (complementarity):
- T2: No theory can decide all bits of Ω (since that would decide all of H*).
- T3: Each theory captures only a fragment of Ω; extensions add more bits.

**Design**: We define OmegaBit as a Prop (not Bool) — fully computable at type level.
-/

namespace Omega

-- ==============================================================================================
-- 1. Setup: ComputabilityModel and RealHalts
-- ==============================================================================================

variable (M : ComputabilityModel)

-- Injection of natural numbers into codes. Each n corresponds to "program n".
variable (embed : ℕ → M.Code)

-- ==============================================================================================
-- 2. OmegaBit: The n-th bit of Ω is RealHalts(embed n)
-- ==============================================================================================

/--
  **OmegaBit**: The n-th bit of Ω is a Prop.
  OmegaBit n holds iff the embedded code halts.

  This is purely propositional — no computation involved.
-/
def OmegaBit (n : ℕ) : Prop :=
  ModelHalts M (embed n)

-- ==============================================================================================
-- 3. Specification Lemmas: Ω as a cut of H*
-- ==============================================================================================

/--
  **OmegaBit is exactly RealHalts**: By definition, trivially.
-/
lemma OmegaBit_iff (n : ℕ) :
    OmegaBit M embed n ↔ ModelHalts M (embed n) :=
  Iff.rfl

/--
  **Negation of OmegaBit is non-halting**.
-/
lemma not_OmegaBit_iff (n : ℕ) :
    ¬ OmegaBit M embed n ↔ ¬ ModelHalts M (embed n) :=
  Iff.rfl

-- ==============================================================================================
-- 4. Connection to TuringGodelContext'
-- ==============================================================================================

/--
  The Turing-Gödel context derived from M.
  In this context, RealHalts = ModelHalts M.
-/
def ctx : TuringGodelContext' M.Code (HaltProp M) :=
  TuringGodelFromModel M

/--
  **Corollary of T2**: No internal predicate can decide all bits of Ω.

  Since each bit of Ω is an instance of RealHalts, and T2 says no internal predicate
  can be total+correct+complete for RealHalts, no theory can decide all of Ω.
-/
theorem T2_applies_to_Omega :
    ¬ ∃ _ : InternalHaltingPredicate (ctx M), True :=
  T2_impossibility (ctx M)

-- ==============================================================================================
-- 5. Ω as instance family for T3
-- ==============================================================================================

/--
  Each bit of Ω corresponds to a HaltProp statement.
  If OmegaBit n holds, we encode it as "halts"; otherwise as "notHalts".
-/
def OmegaHaltProp_halts (n : ℕ) : HaltProp M :=
  HaltProp.halts (embed n)

def OmegaHaltProp_notHalts (n : ℕ) : HaltProp M :=
  HaltProp.notHalts (embed n)

/--
  The Ω-derived HaltProp for halting case is provable when OmegaBit holds.
-/
lemma OmegaHaltProp_halts_provable (n : ℕ) (h : OmegaBit M embed n) :
    HaltProvable M (OmegaHaltProp_halts M embed n) := by
  unfold OmegaHaltProp_halts HaltProvable OmegaBit at *
  exact h

/--
  The Ω-derived HaltProp for non-halting case is provable when OmegaBit fails.
-/
lemma OmegaHaltProp_notHalts_provable (n : ℕ) (h : ¬ OmegaBit M embed n) :
    HaltProvable M (OmegaHaltProp_notHalts M embed n) := by
  unfold OmegaHaltProp_notHalts HaltProvable OmegaBit at *
  exact h
-- ==============================================================================================
-- 6. Internal predicate on Ω bits
-- ==============================================================================================

/--
  An internal predicate on the bits of Ω:

  - `B n` is the internal formula claiming to decide Ω(n)
  - `total`: the system proves B n or ¬ B n for all n
  - `correct`: if Ω(n) is true, then B n is provable
  - `complete`: if Ω(n) is false, then ¬ B n is provable
-/
structure InternalOmegaPredicate
    (M : ComputabilityModel) (embed : ℕ → M.Code) where
  B : ℕ → HaltProp M
  total :
    ∀ n,
      (ctx M).Provable (B n) ∨
      (ctx M).Provable ((ctx M).Not (B n))
  correct :
    ∀ n, OmegaBit M embed n → (ctx M).Provable (B n)
  complete :
    ∀ n, ¬ OmegaBit M embed n → (ctx M).Provable ((ctx M).Not (B n))

-- ==============================================================================================
-- 7. From predicate on Ω → halting predicate
-- ==============================================================================================

section Conversion

variable (M : ComputabilityModel)
variable (embed : ℕ → M.Code)

/--
  From an InternalOmegaPredicate + an index function (inverse of embed),
  we construct an InternalHaltingPredicate.

  Note: `idx` is the explicit function e ↦ n such that embed(idx(e)) = e.
  This function is provided as a parameter.
-/
def InternalOmegaPredicate.toInternalHaltingPredicate
    (idx : M.Code → ℕ)
    (idx_spec : ∀ e, embed (idx e) = e)
    (I : InternalOmegaPredicate M embed) :
    InternalHaltingPredicate (ctx M) where
  H := fun e => I.B (idx e)
  total := fun e => I.total (idx e)
  correct := fun e hReal => by
    -- hReal : (ctx M).RealHalts e = ModelHalts M e
    change ModelHalts M e at hReal
    have hReal' : ModelHalts M (embed (idx e)) := by
      rw [idx_spec e]; exact hReal
    have hOmega : OmegaBit M embed (idx e) := (OmegaBit_iff M embed (idx e)).mpr hReal'
    exact I.correct _ hOmega
  complete := fun e hNotReal => by
    change ¬ ModelHalts M e at hNotReal
    have hNotReal' : ¬ ModelHalts M (embed (idx e)) := by
      rw [idx_spec e]; exact hNotReal
    have hNotOmega : ¬ OmegaBit M embed (idx e) := (not_OmegaBit_iff M embed (idx e)).mpr hNotReal'
    exact I.complete _ hNotOmega

end Conversion

-- ==============================================================================================
-- 8. Final theorem: no internal total/correct/complete predicate for Ω
-- ==============================================================================================

/--
  **Theorem:** If there exists an index function `idx` such that `embed(idx(e)) = e`,
  then there is no internal predicate on the bits of Ω that is total, correct, and complete.
  Otherwise, we would obtain an InternalHaltingPredicate, contradicting T2.
-/
theorem no_internal_omega_predicate
    (idx : M.Code → ℕ)
    (idx_spec : ∀ e, embed (idx e) = e) :
    ¬ ∃ _ : InternalOmegaPredicate M embed, True := by
  intro h
  rcases h with ⟨I, _⟩
  -- Construct an InternalHaltingPredicate from I
  let J := InternalOmegaPredicate.toInternalHaltingPredicate M embed idx idx_spec I
  -- T2 says such a J cannot exist
  have hT2 : ¬ ∃ _ : InternalHaltingPredicate (ctx M), True := T2_applies_to_Omega (M := M)
  exact hT2 ⟨J, trivial⟩

end Omega
