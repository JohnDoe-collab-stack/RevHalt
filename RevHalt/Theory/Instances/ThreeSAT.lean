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

/-- Fuel-bounded list decoder (total). -/
def decodeListAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
      if _h : n = 0 then []
      else
        let a := unpair_fst n
        let b := unpair_snd n
        if _ha : a = 0 then []
        else (a - 1) :: decodeListAux fuel b

/-- Decode a natural to a list of naturals. -/
def decodeList (n : ℕ) : List ℕ :=
  decodeListAux (n + 1) n

lemma pair_pos {a b : ℕ} (ha : a > 0) : pair a b > 0 := by
  simp only [pair]
  have h := Nat.left_le_pair a b
  omega

@[simp] lemma unpair_fst_pair (a b : ℕ) : unpair_fst (pair a b) = a := by
  simp only [unpair_fst, pair, Nat.unpair_pair]

@[simp] lemma unpair_snd_pair (a b : ℕ) : unpair_snd (pair a b) = b := by
  simp only [unpair_snd, pair, Nat.unpair_pair]

lemma right_lt_pair_of_left_pos {a b : ℕ} (ha : 0 < a) : b < pair a b := by
  by_cases h : a < b
  · have hpair : pair a b = b * b + a := by
      simp [pair, Nat.pair, h]
    rw [hpair]
    have hbPos : 0 < b := lt_trans ha h
    have hb1 : 1 ≤ b := Nat.succ_le_iff.mp hbPos
    have hbLeBB : b ≤ b * b := by
      simpa [Nat.mul_one] using (Nat.mul_le_mul_left b hb1)
    have hBBlt : b * b < b * b + a :=
      Nat.lt_add_of_pos_right (n := b * b) (k := a) ha
    exact lt_of_le_of_lt hbLeBB hBBlt
  · have hpair : pair a b = a * a + a + b := by
      simp [pair, Nat.pair, h]
    rw [hpair]
    have haPos' : 0 < a * a + a := Nat.add_pos_right (a * a) ha
    have hbLt : b < (a * a + a) + b :=
      Nat.lt_add_of_pos_left (n := b) (k := a * a + a) haPos'
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbLt

lemma decodeListAux_encodeList (xs : List ℕ) (fuel : ℕ) :
    encodeList xs + 1 ≤ fuel →
    decodeListAux fuel (encodeList xs) = xs := by
  intro hFuel
  induction xs generalizing fuel with
  | nil =>
      cases fuel <;> simp [encodeList, decodeListAux]
  | cons x xs ih =>
      cases fuel with
      | zero =>
          exfalso
          exact Nat.not_succ_le_zero (encodeList (x :: xs)) (by simpa using hFuel)
      | succ fuel' =>
          have hne : pair (x + 1) (encodeList xs) ≠ 0 := by
            have : pair (x + 1) (encodeList xs) > 0 := pair_pos (Nat.succ_pos x)
            omega
          have ha : unpair_fst (pair (x + 1) (encodeList xs)) ≠ 0 := by
            simpa [unpair_fst_pair] using (Nat.succ_ne_zero x)
          have hFuel' : encodeList xs + 1 ≤ fuel' := by
            have hnLe : pair (x + 1) (encodeList xs) ≤ fuel' := by
              exact Nat.succ_le_succ_iff.mp (by simpa [encodeList] using hFuel)
            have hbLe : encodeList xs + 1 ≤ pair (x + 1) (encodeList xs) :=
              Nat.succ_le_iff.mpr (right_lt_pair_of_left_pos (a := x + 1) (b := encodeList xs) (Nat.succ_pos x))
            exact le_trans hbLe hnLe
          have hTail := ih fuel' hFuel'
          simp [encodeList, decodeListAux, dif_neg hne, unpair_fst_pair, unpair_snd_pair, hTail]

@[simp] lemma decodeList_encodeList (xs : List ℕ) : decodeList (encodeList xs) = xs := by
  exact decodeListAux_encodeList xs (encodeList xs + 1) (by exact le_rfl)

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
