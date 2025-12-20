import RevHalt.Base
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic

/-!
# RevHalt.Theory.ComplexityPRevHalt

Bounded P version connected to RevHalt:
- Produces a **Decision** with a **certificate** (like your Python `cert` objects).
- Enforces an 'anti-cheat' rule:
  - `logic = Witness`  ⇒ verdict = HALTS + witness `n ≤ k` with `T n = true`
  - `logic = Exhaustive` ⇒ verdict = NOHALT + local proof `∀ n ≤ k, T n = false`
- Also attaches a **cost certificate**: `cost = k+1` and a polynomial bound (degree 1).

It is intentionally verbose:
- each verdict comes with an actionable proof (witness or exhaustive),
- and correctness can be verified **without an oracle**.
-/

namespace RevHalt.Theory.ComplexityPRevHalt

-- ============================================================================
-- 1) Bool Traces + Bounded Halting
-- ============================================================================

/-- Decidable (computable) trace: ℕ → Bool. -/
def BoolTrace := ℕ → Bool

/-- Bounded Halting (Bool): ∃ n ≤ k, T n = true. -/
def HaltsBool_bounded (T : BoolTrace) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ T n = true

-- ============================================================================
-- 2) Verdict + Certificate Logic (RevHalt style)
-- ============================================================================

/-- Binary verdict (here, no UNKNOWN: the problem is bounded hence decidable). -/
inductive Verdict where
  | HALTS : Verdict
  | NOHALT : Verdict
deriving DecidableEq

/-- Logic type used to justify the verdict (like your `logic` tags). -/
inductive Logic where
  | Witness    : Logic     -- I have a witness n
  | Exhaustive : Logic     -- I have checked all n ≤ k
deriving DecidableEq

/-- Internal certificate data, indexed by logic type. -/
def CertData (T : BoolTrace) (k : ℕ) : Logic → Type
  | Logic.Witness    => { n : ℕ // n ≤ k ∧ T n = true }
  | Logic.Exhaustive => PLift (∀ n, n ≤ k → T n = false)

/-- Certificate (logic + adapted data). -/
structure Cert (T : BoolTrace) (k : ℕ) where
  logic : Logic
  data  : CertData T k logic

/-- 'RevHalt-like' Decision: verdict + cert + cost (certified). -/
structure Decision (T : BoolTrace) (k : ℕ) where
  verdict : Verdict
  cert    : Cert T k
  cost    : ℕ
  cost_eq : cost = k + 1

-- ============================================================================
-- 3) Certificate Anti-Cheat Verification
-- ============================================================================

/--
`verify_cert` enforces 'A/B' (anti-cheat) rules:

- Rule A: if `logic = Witness` then verdict = HALTS
- Rule B: if `logic = Exhaustive` then verdict = NOHALT

Remark: the 'purely local' part (T n = true / ∀ n ≤ k, T n = false)
is already contained in `cert.data` (so impossible to 'forget').
-/
def verify_cert {T : BoolTrace} {k : ℕ} (d : Decision T k) : Prop :=
  match d.cert.logic with
  | Logic.Witness    => d.verdict = Verdict.HALTS
  | Logic.Exhaustive => d.verdict = Verdict.NOHALT

-- ============================================================================
-- 4) Constructive Decider with Certificate Extraction (Witness or Exhaustive)
-- ============================================================================

/--
`findWitness T k` searches for an n in [0..k] such that T n = true,
and returns `some n` if found, else `none`.

This is not an 'oracle': it is a bounded scan.
-/
def findWitness (T : BoolTrace) : ℕ → Option ℕ
  | 0 =>
      if T 0 = true then
        some 0
      else
        none
  | n + 1 =>
      match findWitness T n with
      | some w => some w
      | none =>
          if T (n + 1) = true then
            some (n + 1)
          else
            none

-- ----------------------------------------------------------------------------
-- findWitness Correctness Lemmas
-- ----------------------------------------------------------------------------

/-- If `findWitness T k = some n`, then `n ≤ k` and `T n = true`. -/
theorem findWitness_some_valid (T : BoolTrace) :
    ∀ k n, findWitness T k = some n → n ≤ k ∧ T n = true := by
  intro k
  induction k with
  | zero =>
      intro n h
      unfold findWitness at h
      by_cases h0 : T 0 = true
      · -- branch some 0
        simp [h0] at h
        cases h
        exact And.intro (Nat.le_refl 0) h0
      · -- branch none impossible
        simp [h0] at h
  | succ k ih =>
      intro n h
      unfold findWitness at h
      cases hw : findWitness T k with
      | some w =>
          -- function returns some w, so n = w
          simp [hw] at h
          subst h
          have hwv : w ≤ k ∧ T w = true := ih w hw
          exact And.intro (Nat.le_trans hwv.1 (Nat.le_succ k)) hwv.2
      | none =>
          -- check T (k+1)
          by_cases hk1 : T (k + 1) = true
          · simp [hw, hk1] at h
            subst h
            exact And.intro (Nat.le_refl (k + 1)) hk1
          · simp [hw, hk1] at h

/-- If `findWitness T k = none`, then `∀ n ≤ k, T n = false`. -/
theorem findWitness_none_allfalse (T : BoolTrace) :
    ∀ k, findWitness T k = none → ∀ n, n ≤ k → T n = false := by
  intro k
  induction k with
  | zero =>
      intro hnone n hnle
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnle
      subst hn0
      unfold findWitness at hnone
      by_cases h0 : T 0 = true
      · simp [h0] at hnone
      · -- h0 : T 0 ≠ true  => T 0 = false
        -- on Bool, if ≠ true then = false
        exact Bool.eq_false_iff.mpr h0
  | succ k ih =>
      intro hnone n hnle
      unfold findWitness at hnone
      cases hw : findWitness T k with
      | some w =>
          -- impossible: if findWitness k = some w, findWitness (k+1) cannot be none
          simp [hw] at hnone
      | none =>
          -- then we are in the test of T (k+1)
          by_cases hk1 : T (k + 1) = true
          · simp [hw, hk1] at hnone
          · -- hnone forces T(k+1) ≠ true and findWitness k = none
            have hPrev : findWitness T k = none := hw
            have hallPrev : ∀ m, m ≤ k → T m = false := ih hPrev
            -- case on n: n ≤ k or n = k+1
            have hcases : n ≤ k ∨ n = k + 1 := by
              exact Nat.le_or_eq_of_le_succ hnle
            cases hcases with
            | inl hnle_k =>
                exact hallPrev n hnle_k
            | inr hnEq =>
                subst hnEq
                -- hk1 : T (k+1) ≠ true  => T(k+1)=false
                exact Bool.eq_false_iff.mpr hk1

-- ----------------------------------------------------------------------------
-- Construct Complete Decision (Cert + Cost)
-- ----------------------------------------------------------------------------

/-- Constructor for HALTS case. -/
def mkDecision_halts (T : BoolTrace) (k n : ℕ)
    (hValid : n ≤ k ∧ T n = true) : Decision T k where
  verdict := Verdict.HALTS
  cert := { logic := Logic.Witness, data := ⟨n, hValid⟩ }
  cost := k + 1
  cost_eq := rfl

/-- Constructor for NOHALT case. -/
def mkDecision_nohalt (T : BoolTrace) (k : ℕ)
    (hAll : ∀ n, n ≤ k → T n = false) : Decision T k where
  verdict := Verdict.NOHALT
  cert := { logic := Logic.Exhaustive, data := ⟨hAll⟩ }
  cost := k + 1
  cost_eq := rfl

/-- The cost of mkDecision_halts is k+1. -/
theorem mkDecision_halts_cost (T : BoolTrace) (k n : ℕ) (hValid : n ≤ k ∧ T n = true) :
    (mkDecision_halts T k n hValid).cost = k + 1 := rfl

/-- The cost of mkDecision_nohalt is k+1. -/
theorem mkDecision_nohalt_cost (T : BoolTrace) (k : ℕ) (hAll : ∀ n, n ≤ k → T n = false) :
    (mkDecision_nohalt T k hAll).cost = k + 1 := rfl

/-- verify_cert for mkDecision_halts. -/
theorem mkDecision_halts_verified (T : BoolTrace) (k n : ℕ) (hValid : n ≤ k ∧ T n = true) :
    verify_cert (mkDecision_halts T k n hValid) := rfl

/-- verify_cert for mkDecision_nohalt. -/
theorem mkDecision_nohalt_verified (T : BoolTrace) (k : ℕ) (hAll : ∀ n, n ≤ k → T n = false) :
    verify_cert (mkDecision_nohalt T k hAll) := rfl

/--
Bounded Decider 'RevHalt-like':
- if it finds a witness: verdict HALTS + cert logic=Witness
- otherwise: verdict NOHALT + cert logic=Exhaustive
- certified cost = k+1
-/
def decide_bounded (T : BoolTrace) (k : ℕ) : Decision T k :=
  match hw : findWitness T k with
  | some n => mkDecision_halts T k n (findWitness_some_valid T k n hw)
  | none => mkDecision_nohalt T k (findWitness_none_allfalse T k hw)

-- ============================================================================
-- 5) Soundness: certificate implies verdict truth
-- ============================================================================

/-- If decision is HALTS, we indeed get `HaltsBool_bounded`. -/
theorem decision_HALTS_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.HALTS → HaltsBool_bounded T k := by
  unfold decide_bounded
  split
  · next n hw =>
    intro _
    have hValid := findWitness_some_valid T k n hw
    exact ⟨n, hValid⟩
  · next hw =>
    intro hV
    -- contradiction
    contradiction

/-- If decision is NOHALT, then there is no witness ≤ k. -/
theorem decision_NOHALT_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.NOHALT → ¬ HaltsBool_bounded T k := by
  unfold decide_bounded
  split
  · next n hw =>
    intro hV
    contradiction
  · next hw =>
    intro hV hEx
    rcases hEx with ⟨n, hnle, hntrue⟩
    have hAll := findWitness_none_allfalse T k hw
    have := hAll n hnle
    rw [this] at hntrue
    exact Bool.false_ne_true hntrue

-- ============================================================================
-- 6) Anti-Cheat: verify_cert holds for the produced decision
-- ============================================================================

/-- The decider always produces a certificate compliant with rules A/B. -/
theorem decide_bounded_verified (T : BoolTrace) (k : ℕ) :
    verify_cert (decide_bounded T k) := by
  unfold decide_bounded
  split
  · exact mkDecision_halts_verified _ _ _ _
  · exact mkDecision_nohalt_verified _ _ _

-- ============================================================================
-- 7) Cost Certificate: cost = k+1 and polynomial bound (degree 1)
-- ============================================================================

/-- By construction, cost is exactly k+1. -/
theorem decide_bounded_cost_eq (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).cost = k + 1 := by
  unfold decide_bounded
  split
  · exact mkDecision_halts_cost _ _ _ _
  · exact mkDecision_nohalt_cost _ _ _

/-- Trivial polynomial bound: cost ≤ (k+1)^1. -/
theorem decide_bounded_cost_poly1 (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).cost ≤ (k + 1) ^ (1 : ℕ) := by
  rw [decide_bounded_cost_eq]
  rw [Nat.pow_one]

end RevHalt.Theory.ComplexityPRevHalt
