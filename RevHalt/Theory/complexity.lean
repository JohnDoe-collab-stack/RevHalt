import RevHalt.Base
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic

/-!
# RevHalt.Theory.ComplexityPRevHaltPlus

P (bounded) in RevHalt style:

- Total decision on `[0..k]`.
- Output = `Decision` with **locally verifiable** certificate (anti-cheat).
- Certified cost: `cost = k+1` (bounded scan).

## Philosophy (RevHalt-like)

- `logic = Witness`     ⇒ verdict = HALTS + witness `n ≤ k` with `T n = true`
- `logic = Exhaustive`  ⇒ verdict = NOHALT + proof `∀ n ≤ k, T n = false`

## "Not Trivial" Result

1) We obtain a **S2(k) layer** that is totally internalisable (Bounded P).
2) We also prove a "limit" bridge:

`Halts T  ↔  ∃ k, Halts_bounded T k`

i.e., (unbounded) halting is the **directed union** of bounded layers.
This is exactly the reading "difficulty = bound".
-/

namespace RevHalt.Theory.ComplexityPRevHaltPlus

-- =============================================================================
-- 1) Bool Traces + Bridge to RevHalt.Trace
-- =============================================================================

/-- Decidable (computable) trace : ℕ → Bool. -/
def BoolTrace := ℕ → Bool

/-- Conversion to RevHalt trace (Prop) : `T n = true`. -/
def BoolTrace.toTrace (T : BoolTrace) : Trace := fun n => T n = true

/-- Bool Halting (unbounded) : ∃ n, T n = true. -/
def HaltsBool (T : BoolTrace) : Prop := ∃ n, T n = true

/-- Bounded Bool Halting : ∃ n ≤ k, T n = true. -/
def HaltsBool_bounded (T : BoolTrace) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ T n = true

/-- Prop Version (RevHalt-like) : ∃ n ≤ k, T n. -/
def Halts_bounded (T : Trace) (k : ℕ) : Prop :=
  ∃ n, n ≤ k ∧ T n

/-- Bridge : HaltsBool_bounded ↔ Halts_bounded (via toTrace). -/
theorem halts_bounded_bridge (T : BoolTrace) (k : ℕ) :
    HaltsBool_bounded T k ↔ Halts_bounded (T.toTrace) k := by
  unfold HaltsBool_bounded Halts_bounded BoolTrace.toTrace
  rfl

-- =============================================================================
-- 2) Verdict + Logic + Certificate (RevHalt Style)
-- =============================================================================

/-- Binary Verdict (bounded ⇒ no UNKNOWN). -/
inductive Verdict where
  | HALTS : Verdict
  | NOHALT : Verdict
deriving DecidableEq

/-- Certificate "Logic". -/
inductive Logic where
  | Witness    : Logic     -- witness n found
  | Exhaustive : Logic     -- exhaustive scan (no witness ≤ k)
deriving DecidableEq

/-- Certificate Data, indexed by logic. -/
def CertData (T : BoolTrace) (k : ℕ) : Logic → Type
  | Logic.Witness    => { n : ℕ // n ≤ k ∧ T n = true }
  | Logic.Exhaustive => PLift (∀ n, n ≤ k → T n = false)

/-- Certificate = logic tag + adapted data. -/
structure Cert (T : BoolTrace) (k : ℕ) where
  logic : Logic
  data  : CertData T k logic

/-- RevHalt-like Decision : verdict + source + cert + certified cost. -/
structure Decision (T : BoolTrace) (k : ℕ) where
  verdict : Verdict
  source  : String
  cert    : Cert T k
  cost    : ℕ
  cost_eq : cost = k + 1

-- =============================================================================
-- 3) Anti-Cheat Verification (Rules A/B)
-- =============================================================================

/--
Anti-cheat (structural):
- Witness     ⇒ verdict = HALTS
- Exhaustive  ⇒ verdict = NOHALT

Local content (T n = true / ∀ n ≤ k, T n = false) is already in `cert.data`.
-/
def verify_cert {T : BoolTrace} {k : ℕ} (d : Decision T k) : Prop :=
  match d.cert.logic with
  | Logic.Witness    => d.verdict = Verdict.HALTS
  | Logic.Exhaustive => d.verdict = Verdict.NOHALT

-- =============================================================================
-- 4) Bounded Scan: findWitness
-- =============================================================================

/--
`findWitness T k` searches for a witness `n ∈ [0..k]` such that `T n = true`.
-/
def findWitness (T : BoolTrace) : ℕ → Option ℕ
  | 0 =>
      if T 0 = true then some 0 else none
  | n + 1 =>
      match findWitness T n with
      | some w => some w
      | none =>
          if T (n + 1) = true then some (n + 1) else none

/-- If `findWitness T k = some n`, then `n ≤ k` and `T n = true`. -/
theorem findWitness_some_valid (T : BoolTrace) :
    ∀ k n, findWitness T k = some n → n ≤ k ∧ T n = true := by
  intro k
  induction k with
  | zero =>
      intro n h
      unfold findWitness at h
      by_cases h0 : T 0 = true
      · simp [h0] at h
        subst h
        exact ⟨Nat.le_refl 0, h0⟩
      · simp [h0] at h
  | succ k ih =>
      intro n h
      unfold findWitness at h
      cases hw : findWitness T k with
      | some w =>
          simp [hw] at h
          subst h
          have hwv : w ≤ k ∧ T w = true := ih w hw
          exact ⟨Nat.le_trans hwv.1 (Nat.le_succ k), hwv.2⟩
      | none =>
          by_cases hk1 : T (k + 1) = true
          · simp [hw, hk1] at h
            subst h
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
      · simp [h0] at hnone
      · exact Bool.eq_false_iff.mpr h0
  | succ k ih =>
      intro hnone n hnle
      unfold findWitness at hnone
      cases hw : findWitness T k with
      | some w =>
          simp [hw] at hnone
      | none =>
          by_cases hk1 : T (k + 1) = true
          · simp [hw, hk1] at hnone
          ·
            have hallPrev : ∀ m, m ≤ k → T m = false := ih hw
            have hcases : n ≤ k ∨ n = k + 1 := Nat.le_or_eq_of_le_succ hnle
            cases hcases with
            | inl hnle_k =>
                exact hallPrev n hnle_k
            | inr hnEq =>
                cases hnEq
                exact Bool.eq_false_iff.mpr hk1

-- =============================================================================
-- 5) Decision Constructors (HALTS / NOHALT)
-- =============================================================================

private def sourceS2 (k : ℕ) : String :=
  "S2(bounded:" ++ toString k ++ ")"

/-- Constructor HALTS (Witness). -/
def mkDecision_halts (T : BoolTrace) (k n : ℕ)
    (hValid : n ≤ k ∧ T n = true) : Decision T k where
  verdict := Verdict.HALTS
  source  := sourceS2 k
  cert    := { logic := Logic.Witness, data := ⟨n, hValid⟩ }
  cost    := k + 1
  cost_eq := rfl

/-- Constructor NOHALT (Exhaustive). -/
def mkDecision_nohalt (T : BoolTrace) (k : ℕ)
    (hAll : ∀ n, n ≤ k → T n = false) : Decision T k where
  verdict := Verdict.NOHALT
  source  := sourceS2 k
  cert    := { logic := Logic.Exhaustive, data := ⟨hAll⟩ }
  cost    := k + 1
  cost_eq := rfl

/-- Bounded Decider RevHalt-like. -/
def decide_bounded (T : BoolTrace) (k : ℕ) : Decision T k :=
  match hw : findWitness T k with
  | some n => mkDecision_halts T k n (findWitness_some_valid T k n hw)
  | none   => mkDecision_nohalt T k (findWitness_none_allfalse T k hw)

-- =============================================================================
-- 6) Specification : Correctness + Anti-Cheat + Certified Cost
-- =============================================================================

/-- Anti-Cheat: The decider always produces a compliant certificate. -/
theorem decide_bounded_verified (T : BoolTrace) (k : ℕ) :
    verify_cert (decide_bounded T k) := by
  unfold decide_bounded
  split
  next n heq =>
    simp [verify_cert, mkDecision_halts]
  next heq =>
    simp [verify_cert, mkDecision_nohalt]

/-- Certified Cost : cost = k+1. -/
theorem decide_bounded_cost_eq (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).cost = k + 1 := by
  unfold decide_bounded
  split
  next n heq =>
    simp [mkDecision_halts]
  next heq =>
    simp [mkDecision_nohalt]

/-- Soundness (HALTS ⇒ ∃ witness ≤ k). -/
theorem decision_HALTS_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.HALTS → HaltsBool_bounded T k := by
  intro hV
  rw [decide_bounded] at hV
  split at hV
  next n heq =>
    exact ⟨n, findWitness_some_valid T k n heq⟩
  next heq =>
    simp [mkDecision_nohalt] at hV

/-- Soundness (NOHALT ⇒ ¬ ∃ witness ≤ k). -/
theorem decision_NOHALT_sound (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.NOHALT → ¬ HaltsBool_bounded T k := by
  intro hV hHalts
  rw [decide_bounded] at hV
  split at hV
  next n heq =>
    simp [mkDecision_halts] at hV
  next heq =>
    rcases hHalts with ⟨n, hnle, hntrue⟩
    have hAll : ∀ n, n ≤ k → T n = false := findWitness_none_allfalse T k heq
    have : T n = false := hAll n hnle
    rw [this] at hntrue
    exact Bool.false_ne_true hntrue

/-- Full Specification : Verdict HALTS ↔ HaltsBool_bounded. -/
theorem decide_bounded_correct (T : BoolTrace) (k : ℕ) :
    (decide_bounded T k).verdict = Verdict.HALTS ↔ HaltsBool_bounded T k := by
  constructor
  · exact decision_HALTS_sound T k
  · intro hHalts
    -- if verdict was NOHALT, contradiction
    by_contra hNot
    cases hv : (decide_bounded T k).verdict with
    | HALTS =>
        exact hNot hv
    | NOHALT =>
        exact (decision_NOHALT_sound T k hv) hHalts

-- =============================================================================
-- 7) The "Limit Bridge" : Halts = Directed Union of Halts_bounded
-- =============================================================================

/-- Monotonicity in k : if it halts before k, it halts before k'. -/
theorem haltsBool_bounded_mono (T : BoolTrace) {k k' : ℕ} (hkk' : k ≤ k') :
    HaltsBool_bounded T k → HaltsBool_bounded T k' := by
  intro ⟨n, hnle, hntrue⟩
  exact ⟨n, Nat.le_trans hnle hkk', hntrue⟩

/--
**Directed-limit (Bool)** : Unbounded halting ↔ "Exists a bound".

This is the most "limit-chain" form possible without invoking your dynamics:
HaltsBool = ⋃_k HaltsBool_bounded k (at Prop level).
-/
theorem haltsBool_iff_exists_bounded (T : BoolTrace) :
    HaltsBool T ↔ ∃ k, HaltsBool_bounded T k := by
  constructor
  · intro ⟨n, hntrue⟩
    exact ⟨n, ⟨n, Nat.le_refl n, hntrue⟩⟩
  · intro ⟨k, ⟨n, _hnle, hntrue⟩⟩
    exact ⟨n, hntrue⟩

/--
**Directed-limit (Trace/Prop)** : Halts ↔ ∃k, Halts_bounded k.

This is exactly the reading: RE Halting is the colimit
of decidable approximations (P) indexed by k.
-/
theorem halts_iff_exists_bounded (T : Trace) :
    Halts T ↔ ∃ k, Halts_bounded T k := by
  constructor
  · intro ⟨n, hn⟩
    exact ⟨n, ⟨n, Nat.le_refl n, hn⟩⟩
  · intro ⟨k, ⟨n, _hnle, hn⟩⟩
    exact ⟨n, hn⟩

end RevHalt.Theory.ComplexityPRevHaltPlus
