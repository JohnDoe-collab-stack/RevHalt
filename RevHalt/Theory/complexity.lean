import RevHalt.Base
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic

/-!
# RevHalt.Theory.ComplexityPRevHalt


P (bounded) in RevHalt style:
- Total decision on a bounded domain `[0..k]`.
- Output = `Decision` with *locally verifiable* certificate (anti-cheat).

Philosophy:
- `logic = Witness`  ⇒ verdict = HALTS and we provide `n ≤ k` with `T n = true`
- `logic = Exhaustive` ⇒ verdict = NOHALT and we provide `∀ n, n ≤ k → T n = false`
- certified cost : `cost = k+1` (scan on `[0..k]`).

This layer corresponds to a "pure" S2: internalizable, without oracle.
-/

namespace RevHalt.Theory.ComplexityPRevHalt

-- ============================================================================
-- 1) Bool Traces + bridge to RevHalt.Trace
-- ============================================================================

/-- Decidable trace (computable) : ℕ → Bool. -/
def BoolTrace := ℕ → Bool

/-- Conversion to RevHalt trace (Prop): `T n = true`. -/
def BoolTrace.toTrace (T : BoolTrace) : Trace := fun n => T n = true

/-- Bounded Halting (Bool): ∃ n ≤ k, T n = true. -/
def HaltsBool_bounded (T : BoolTrace) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ T n = true

/-- Prop Version (RevHalt-like): ∃ n ≤ k, (Trace n). -/
def Halts_bounded (T : Trace) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ T n

/-- Bridge: HaltsBool_bounded ↔ Halts_bounded (via toTrace). -/
theorem halts_bounded_bridge (T : BoolTrace) (k : ℕ) :
    HaltsBool_bounded T k ↔ Halts_bounded (T.toTrace) k := by
  unfold HaltsBool_bounded Halts_bounded BoolTrace.toTrace
  rfl

-- ============================================================================
-- 2) Verdict + logic + certificate (RevHalt style)
-- ============================================================================

/-- Binary verdict (bounded ⇒ no UNKNOWN). -/
inductive Verdict where
  | HALTS : Verdict
  | NOHALT : Verdict
deriving DecidableEq

/-- Certificate "Logic". -/
inductive Logic where
  | Witness    : Logic     -- witness n found
  | Exhaustive : Logic     -- exhaustive scan (no witness ≤ k)
deriving DecidableEq

/-- Certificate data, indexed by logic. -/
def CertData (T : BoolTrace) (k : ℕ) : Logic → Type
  | Logic.Witness    => { n : ℕ // n ≤ k ∧ T n = true }
  | Logic.Exhaustive => PLift (∀ n, n ≤ k → T n = false)

/-- Certificate = logic tag + adapted data. -/
structure Cert (T : BoolTrace) (k : ℕ) where
  logic : Logic
  data  : CertData T k logic

/-- "RevHalt-like" Decision: verdict + source + cert + certified cost. -/
structure Decision (T : BoolTrace) (k : ℕ) where
  verdict : Verdict
  source  : String
  cert    : Cert T k
  cost    : ℕ
  cost_eq : cost = k + 1

-- ============================================================================
-- 3) Anti-cheat verification (rules A/B)
-- ============================================================================

/--
Anti-cheat (structural):
- Witness ⇒ verdict = HALTS
- Exhaustive ⇒ verdict = NOHALT

The local content (T n = true / ∀ n ≤ k, T n = false) is already in `cert.data`.
-/
def verify_cert {T : BoolTrace} {k : ℕ} (d : Decision T k) : Prop :=
  match d.cert.logic with
  | Logic.Witness    => d.verdict = Verdict.HALTS
  | Logic.Exhaustive => d.verdict = Verdict.NOHALT

-- ============================================================================
-- 4) Bounded scan: findWitness
-- ============================================================================

/--
`findWitness T k` searches for a witness `n ∈ [0..k]` such that `T n = true`.
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
-- Correctness lemmas for findWitness
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
      · -- some 0 = some n
        simp [h0] at h
        cases h
        exact ⟨Nat.le_refl 0, h0⟩
      · -- none = some n impossible
        simp [h0] at h
  | succ k ih =>
      intro n h
      unfold findWitness at h
      cases hw : findWitness T k with
      | some w =>
          simp [hw] at h
          cases h
          have hwv : n ≤ k ∧ T n = true := ih n hw
          exact ⟨Nat.le_trans hwv.1 (Nat.le_succ k), hwv.2⟩
      | none =>
          by_cases hk1 : T (k + 1) = true
          · simp [hw, hk1] at h
            cases h
            exact ⟨Nat.le_refl (k + 1), hk1⟩
          · simp [hw, hk1] at h

/-- If `findWitness T k = none`, then `∀ n ≤ k, T n = false`. -/
theorem findWitness_none_allfalse (T : BoolTrace) :
    ∀ k, findWitness T k = none → ∀ n, n ≤ k → T n = false := by
  intro k
  induction k with
  | zero =>
      intro hnone n hnle
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnle
      cases hn0
      unfold findWitness at hnone
      by_cases h0 : T 0 = true
      · -- some 0 = none impossible
        simp [h0] at hnone
      · -- so T 0 = false
        exact Bool.eq_false_iff.mpr h0
  | succ k ih =>
      intro hnone n hnle
      unfold findWitness at hnone
      cases hw : findWitness T k with
      | some w =>
          -- some w = none impossible
          simp [hw] at hnone
      | none =>
          by_cases hk1 : T (k + 1) = true
          · -- some (k+1) = none impossible
            simp [hw, hk1] at hnone
          · -- everything is false on ≤k, and T(k+1)=false
            have hPrev : findWitness T k = none := hw
            have hallPrev : ∀ m, m ≤ k → T m = false := ih hPrev
            have hcases : n ≤ k ∨ n = k + 1 := Nat.le_or_eq_of_le_succ hnle
            cases hcases with
            | inl hnle_k =>
                exact hallPrev n hnle_k
            | inr hnEq =>
                cases hnEq
                exact Bool.eq_false_iff.mpr hk1

-- ============================================================================
-- 5) Decision Constructors (HALTS / NOHALT)
-- ============================================================================

/-- HALTS Constructor (Witness). -/
def mkDecision_halts (T : BoolTrace) (k n : ℕ)
    (hValid : n ≤ k ∧ T n = true) : Decision T k where
  verdict := Verdict.HALTS
  source  := "S2"
  cert    := { logic := Logic.Witness, data := ⟨n, hValid⟩ }
  cost    := k + 1
  cost_eq := rfl

/-- NOHALT Constructor (Exhaustive). -/
def mkDecision_nohalt (T : BoolTrace) (k : ℕ)
    (hAll : ∀ n, n ≤ k → T n = false) : Decision T k where
  verdict := Verdict.NOHALT
  source  := "S2"
  cert    := { logic := Logic.Exhaustive, data := ⟨hAll⟩ }
  cost    := k + 1
  cost_eq := rfl

/-- RevHalt-like bounded decider. -/
def decide_bounded (T : BoolTrace) (k : ℕ) : Decision T k :=
  match hw : findWitness T k with
  | some n => mkDecision_halts T k n (findWitness_some_valid T k n hw)
  | none   => mkDecision_nohalt T k (findWitness_none_allfalse T k hw)

-- ============================================================================
-- 6) Soundness: the verdict implies (bounded) truth
-- ============================================================================

/-- If the decision says HALTS, then there exists a witness ≤ k. -/
theorem decision_HALTS_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.HALTS → HaltsBool_bounded T k := by
  intro hV
  unfold decide_bounded at hV
  cases hw : findWitness T k with
  | some n =>
      -- ok: we return exactly this witness
      have hValid : n ≤ k ∧ T n = true := findWitness_some_valid T k n hw
      exact ⟨n, hValid⟩
  | none =>
      -- contradiction: in this branch verdict = NOHALT
      split at hV
      · rw [hw] at *; contradiction
      · simp [mkDecision_nohalt] at hV

/-- If the decision says NOHALT, then there exists no witness ≤ k. -/
theorem decision_NOHALT_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.NOHALT → ¬ HaltsBool_bounded T k := by
  intro hV hHalts
  unfold decide_bounded at hV
  cases hw : findWitness T k with
  | some n =>
      -- contradiction: in this branch verdict = HALTS
      split at hV
      · simp [mkDecision_halts] at hV
      · rw [hw] at *; contradiction
  | none =>
      -- we use the exhaustive proof
      rcases hHalts with ⟨n, hnle, hntrue⟩
      have hAll : ∀ n, n ≤ k → T n = false := findWitness_none_allfalse T k hw
      have : T n = false := hAll n hnle
      rw [this] at hntrue
      exact Bool.false_ne_true hntrue

/-- "Equivalence" theorem: HALTS ↔ HaltsBool_bounded. -/
theorem decide_bounded_correct (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.HALTS ↔ HaltsBool_bounded T k := by
  constructor
  · exact decision_HALTS_sound T k
  · intro hHalts
    -- if HaltsBool_bounded, we cannot be NOHALT without contradiction
    by_contra hNot
    have hNo : (decide_bounded T k).verdict = Verdict.NOHALT := by
      cases hV : (decide_bounded T k).verdict with
      | HALTS =>
          -- hNot contradicts the HALTS case
          exfalso
          exact hNot hV
      | NOHALT =>
          exact rfl
    exact (decision_NOHALT_sound T k hNo) hHalts

-- ============================================================================
-- 7) Anti-cheat: the decider always produces a compliant cert
-- ============================================================================

theorem decide_bounded_verified (T : BoolTrace) (k : ℕ) :
    verify_cert (decide_bounded T k) := by
  unfold decide_bounded
  split <;> simp [verify_cert, mkDecision_halts, mkDecision_nohalt]

-- ============================================================================
-- 8) Cost: cost = k+1 and polynomial bound degree 1
-- ============================================================================

theorem decide_bounded_cost_eq (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).cost = k + 1 := by
  unfold decide_bounded
  split <;> simp [mkDecision_halts, mkDecision_nohalt]

theorem decide_bounded_cost_poly1 (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).cost ≤ (k + 1) ^ (1 : ℕ) := by
  -- (k+1)^1 = k+1
  have hc : (decide_bounded T k).cost = k + 1 := decide_bounded_cost_eq T k
  rw [hc, Nat.pow_one]


-- ============================================================================
-- 9) Anti-Cheat Consequences
-- ============================================================================

/--
Universal Anti-Cheat Theorem:
If a decision `d` is verified (i.e. satisfies `verify_cert`), then its verdict
is semantically correct, regardless of how `d` was computed.
-/
theorem verify_cert_correctness {T : BoolTrace} {k : ℕ} (d : Decision T k) (h : verify_cert d) :
    (d.verdict = Verdict.HALTS → HaltsBool_bounded T k) ∧
    (d.verdict = Verdict.NOHALT → ¬ HaltsBool_bounded T k) := by
  cases hL : d.cert.logic
  case Witness =>
    unfold verify_cert at h
    simp [hL] at h
    -- h : d.verdict = Verdict.HALTS
    constructor
    · intro _
      have hData := d.cert.data
      rw [hL] at hData
      exact ⟨hData.val, hData.property⟩
    · intro hV
      rw [h] at hV
      contradiction
  case Exhaustive =>
    unfold verify_cert at h
    simp [hL] at h
    -- h : d.verdict = Verdict.NOHALT
    constructor
    · intro hV
      rw [h] at hV
      contradiction
    · intro _ hHalts
      have hData := d.cert.data
      rw [hL] at hData
      rcases hHalts with ⟨n, hnle, hntrue⟩
      have : T n = false := hData.down n hnle
      rw [this] at hntrue
      contradiction

end RevHalt.Theory.ComplexityPRevHalt
