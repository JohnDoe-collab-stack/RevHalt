import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.Basic

namespace RevHalt.ThreeSAT

open RevHalt

/-
  Minimal, constructive 3-SAT instance:
  - Code := ℕ
  - PropT := ℕ
  - Witness := List ℕ of bits (0/1), length = nVars
  - Machine_3SAT enumerates codes < k, decodes as witness, checks satisfiable
-/

-- ===== List encoding (copy of the constructive pattern used in TSP) =====

abbrev pair := Nat.pair
abbrev unpair_fst (n : ℕ) : ℕ := (Nat.unpair n).1
abbrev unpair_snd (n : ℕ) : ℕ := (Nat.unpair n).2

def encodeList : List ℕ → ℕ
  | [] => 0
  | x :: xs => pair (x + 1) (encodeList xs)

-- We reuse a simple "invalid -> []" total decoder; termination via decreasing snd.
lemma unpair_snd_lt_of_pos {n : ℕ} (hn : n > 0) (_ha : unpair_fst n > 0) : unpair_snd n < n := by
  simp only [unpair_snd]
  set a := (Nat.unpair n).1 with ha_def
  set b := (Nat.unpair n).2 with hb_def
  have heq : Nat.pair a b = n := Nat.pair_unpair n
  -- b ≤ pair a b = n
  have h_le : b ≤ Nat.pair a b := Nat.right_le_pair a b
  rw [heq] at h_le
  -- Need b < n. If b = n, then pair a b = b, which is only possible when a = 0 and b = 0
  rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
  · exact h_lt
  · exfalso
    -- b = n and pair a b = n, so pair a b = b
    have hpair_eq : Nat.pair a b = b := by rw [heq, h_eq]
    -- pair a b = if a < b then b*b + a else a*a + a + b
    simp only [Nat.pair] at hpair_eq
    split_ifs at hpair_eq with hcmp
    · -- hpair_eq : b * b + a = b
      -- Since b * b + a = b and a ≥ 0, we need b * b ≤ b, i.e., b * (b - 1) ≤ 0
      -- For natural numbers, this means b ≤ 1
      -- Case b = 0: then a = 0
      -- Case b = 1: then 1 + a = 1, so a = 0
      -- Either way, a = 0, but _ha says a > 0, contradiction
      simp only [unpair_fst, ← ha_def] at _ha
      have hb_bound : b ≤ 1 := by
        by_contra h
        push_neg at h
        -- b ≥ 2, so b * b ≥ 4 > b, contradiction with hpair_eq
        have : b * b ≥ 2 * b := Nat.mul_le_mul_right b h
        omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb_bound with hb0 | hb1
      · simp [hb0] at hpair_eq; omega
      · simp [hb1] at hpair_eq; omega
    · -- hpair_eq : a * a + a + b = b
      -- So a * a + a = 0, i.e., a * (a + 1) = 0
      -- Since a + 1 > 0, we must have a = 0
      simp only [unpair_fst, ← ha_def] at _ha
      have ha0 : a = 0 := by
        have heq : a * (a + 1) = 0 := by omega
        cases Nat.mul_eq_zero.mp heq with
        | inl h => exact h
        | inr h => omega  -- a + 1 = 0 is impossible
      omega



def decodeList (n : ℕ) : List ℕ :=
  if h : n = 0 then []
  else
    let a := unpair_fst n
    let b := unpair_snd n
    if ha : a = 0 then []
    else (a - 1) :: decodeList b
termination_by n
decreasing_by
  exact unpair_snd_lt_of_pos (Nat.pos_of_ne_zero h) (Nat.pos_of_ne_zero ha)

@[simp] lemma decodeList_encodeList (xs : List ℕ) : decodeList (encodeList xs) = xs := by
  induction xs with
  | nil =>
      simp [encodeList, decodeList]
  | cons x xs ih =>
      unfold encodeList
      have hne : pair (x + 1) (encodeList xs) ≠ 0 := by
        -- Nat.pair is never 0 with left component > 0
        intro h0
        have : (x + 1) = 0 := by
          -- Nat.left_le_pair: a ≤ pair a b
          apply Nat.eq_zero_of_le_zero
          have h1 := Nat.left_le_pair (x + 1) (encodeList xs)
          have h2 : Nat.pair (x + 1) (encodeList xs) ≤ 0 := Nat.le_of_eq h0
          exact h1.trans h2
        exact Nat.succ_ne_zero x this
      simp [decodeList, dif_neg hne, unpair_fst, unpair_snd, ih]

-- ===== 3SAT syntax =====

abbrev LitCode := ℕ
def litVar (l : LitCode) : ℕ := unpair_fst l
def litNeg (l : LitCode) : ℕ := unpair_snd l   -- intended: 0 or 1

structure ThreeSATInstance where
  nVars : ℕ
  clauses : List (List LitCode)

-- ===== Validity checks (computable) =====

def isBit (b : ℕ) : Bool := decide (b = 0 ∨ b = 1)

def litValid (n : ℕ) (l : LitCode) : Bool :=
  (decide (litVar l < n)) && (decide (litNeg l ≤ 1))

def clauseValid (n : ℕ) (c : List LitCode) : Bool :=
  (decide (c.length = 3)) && (c.all (fun l => litValid n l))

def instValid (inst : ThreeSATInstance) : Bool :=
  (decide (inst.nVars > 0)) && (inst.clauses.all (fun c => clauseValid inst.nVars c))

-- ===== Encoding/decoding instance code =====
-- code := pair nVars (encodeList (clauses.map encodeList))
-- where each clause is itself encoded as a list of literal codes.

def encodeClause (c : List LitCode) : ℕ := encodeList c
def decodeClause (n : ℕ) : List LitCode := decodeList n

def encodeCNF (cs : List (List LitCode)) : ℕ :=
  encodeList (cs.map encodeClause)

def decodeCNF (n : ℕ) : List (List LitCode) :=
  (decodeList n).map decodeClause

def encode3SAT (inst : ThreeSATInstance) : ℕ :=
  pair inst.nVars (encodeCNF inst.clauses)

def decode3SAT (p : ℕ) : Option ThreeSATInstance :=
  let n := unpair_fst p
  let f := unpair_snd p
  let inst : ThreeSATInstance := { nVars := n, clauses := decodeCNF f }
  if instValid inst then some inst else none

-- ===== Semantics (computable) =====

def bitAt (w : List ℕ) (i : ℕ) : Bool :=
  decide ((w.getD i 0) = 1)

def evalLit (w : List ℕ) (l : LitCode) : Bool :=
  let v := litVar l
  let b := bitAt w v
  if litNeg l = 0 then b else (!b)

def evalClause (w : List ℕ) (c : List LitCode) : Bool :=
  c.any (fun l => evalLit w l)

def evalCNFInst (inst : ThreeSATInstance) (w : List ℕ) : Bool :=
  inst.clauses.all (fun c => evalClause w c)

def checkAssignment (inst : ThreeSATInstance) (w : List ℕ) : Bool :=
  (decide (w.length = inst.nVars)) && (w.all isBit)

def satWitness (inst : ThreeSATInstance) (w : List ℕ) : Bool :=
  (checkAssignment inst w) && (evalCNFInst inst w)

def HasSolution (inst : ThreeSATInstance) : Prop :=
  ∃ w : List ℕ, satWitness inst w = true

-- ===== Machine =====

def Machine_3SAT (code : ℕ) : Trace :=
  fun k =>
    match decode3SAT code with
    | none => False
    | some inst =>
        ∃ wCode < k,
          satWitness inst (decodeList wCode) = true

theorem Machine_3SAT_halts_iff {code : ℕ} {inst : ThreeSATInstance}
    (hdec : decode3SAT code = some inst) :
    Halts (Machine_3SAT code) ↔ HasSolution inst := by
  constructor
  · intro hH
    rcases hH with ⟨k, hk⟩
    simp [Machine_3SAT, hdec] at hk
    rcases hk with ⟨wCode, _, hw⟩
    refine ⟨decodeList wCode, ?_⟩
    exact hw
  · intro hSol
    rcases hSol with ⟨w, hw⟩
    -- choose witness code as encodeList w
    let wCode := encodeList w
    refine ⟨wCode + 1, ?_⟩
    simp [Machine_3SAT, hdec]
    refine ⟨wCode, Nat.lt_succ_self _, ?_⟩
    simpa [wCode, decodeList_encodeList] using hw

end RevHalt.ThreeSAT
