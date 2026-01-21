import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.TheoryDynamics_ProofCarrying
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

/-!
`Nat.unpair_pair` currently depends on `Classical.choice`/`Quot.sound` in Mathlib.
For the 3SAT instance we need a constructive roundtrip `decodeList (encodeList xs) = xs`
inside the main halting lemma, so we use a pairing based on 2-adic factorization:

  `pair a b = 2^a * (2*b + 1)`

and decode by stripping factors of 2 using a fuel-bounded loop (total, constructive).
-/

/-- Pairing function (2-adic). -/
def pair (a b : ℕ) : ℕ := Nat.pow 2 a * (2 * b + 1)

lemma pair_ne_zero (a b : ℕ) : pair a b ≠ 0 := by
  have hpow : Nat.pow 2 a ≠ 0 := by
    exact Nat.ne_of_gt (pow_pos (by decide : (0 : ℕ) < 2) a)
  have hodd : (2 * b + 1) ≠ 0 := by
    exact Nat.succ_ne_zero (2 * b)
  exact Nat.mul_ne_zero hpow hodd

lemma pair_pos (a b : ℕ) : 0 < pair a b := by
  have hpow : 0 < Nat.pow 2 a := pow_pos (by decide : (0 : ℕ) < 2) a
  have hodd : 0 < (2 * b + 1) := Nat.succ_pos (2 * b)
  exact Nat.mul_pos hpow hodd

lemma le_pow_two (a : ℕ) : a ≤ Nat.pow 2 a := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      have hOne : 1 ≤ Nat.pow 2 a := by
        simpa using (Nat.one_le_pow a 2)
      have hStep1 : a + 1 ≤ Nat.pow 2 a + 1 := Nat.succ_le_succ ih
      have hStep2 : Nat.pow 2 a + 1 ≤ Nat.pow 2 a + Nat.pow 2 a :=
        Nat.add_le_add_left hOne (Nat.pow 2 a)
      have hStep3 : a + 1 ≤ Nat.pow 2 a + Nat.pow 2 a := le_trans hStep1 hStep2
      -- `2^(a+1) = 2^a * 2 = 2^a + 2^a`
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_two, Nat.add_assoc] using hStep3

lemma right_lt_pair_of_left_pos {a b : ℕ} : b < pair a b := by
  have hb_le : b ≤ 2 * b := by
    have h : b * 1 ≤ b * 2 := Nat.mul_le_mul_left b (by decide : (1 : ℕ) ≤ 2)
    have h' := h
    rw [Nat.mul_one] at h'
    have h'' := h'
    rw [Nat.mul_comm b 2] at h''
    exact h''
  have hb_lt : b < 2 * b + 1 := Nat.lt_succ_of_le hb_le
  have hPow : 1 ≤ Nat.pow 2 a := by
    -- `Nat.one_le_pow` avoids any classical reasoning.
    simpa using (Nat.one_le_pow a 2 (by decide : 0 < (2 : ℕ)))
  have hMul : (2 * b + 1) ≤ pair a b := by
    -- (2*b+1) = 1*(2*b+1) ≤ (2^a)*(2*b+1) = pair a b
    have h0 : 1 * (2 * b + 1) ≤ Nat.pow 2 a * (2 * b + 1) :=
      Nat.mul_le_mul_right (2 * b + 1) hPow
    have h1 := h0
    rw [Nat.one_mul] at h1
    -- rewrite the target to match `pair`
    rw [pair]
    exact h1
  exact lt_of_lt_of_le hb_lt hMul

/-- Fuel-bounded decomposition of a natural into `2^a * odd`. -/
def unpairAux : ℕ → ℕ → ℕ × ℕ
  | 0, n => (0, n)
  | fuel + 1, n =>
      if n % 2 = 0 then
        let p := unpairAux fuel (n / 2)
        (p.1 + 1, p.2)
      else (0, n)

def unpair (n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0, 0)
  else
    let p := unpairAux (n + 1) n
    (p.1, (p.2 - 1) / 2)

abbrev unpair_fst (n : ℕ) : ℕ := (unpair n).1
abbrev unpair_snd (n : ℕ) : ℕ := (unpair n).2

lemma pair_succ_left (a b : ℕ) : pair (a + 1) b = 2 * pair a b := by
  simp [pair, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]

lemma unpairAux_pair (a b fuel : ℕ) (hFuel : a + 1 ≤ fuel) :
    unpairAux fuel (pair a b) = (a, 2 * b + 1) := by
  induction a generalizing fuel with
  | zero =>
      -- pair 0 b is odd, so unpairAux stops immediately (even with fuel=0)
      cases fuel with
      | zero =>
          simp [unpairAux, pair]
      | succ fuel' =>
          -- pair 0 b is odd, so unpairAux stops immediately.
          simp [unpairAux, pair]
  | succ a ih =>
      cases fuel with
      | zero =>
          -- `a + 2 ≤ 0` is impossible.
          exfalso
          exact Nat.not_succ_le_zero (Nat.succ a) hFuel
      | succ fuel' =>
          have hFuel' : a + 1 ≤ fuel' := by
            -- (a+2 ≤ fuel'+1) -> (a+1 ≤ fuel')
            exact Nat.succ_le_succ_iff.mp (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hFuel)
          have hEven : pair (a + 1) b % 2 = 0 := by
            simp [pair_succ_left]
          have hDiv : pair (a + 1) b / 2 = pair a b := by
            simp [pair_succ_left]
          have hRec : unpairAux fuel' (pair a b) = (a, 2 * b + 1) := ih fuel' hFuel'
          simp [unpairAux, hEven, hDiv, hRec]

@[simp] lemma unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  have hne : pair a b ≠ 0 := pair_ne_zero a b
  have hFuel : a + 1 ≤ pair a b + 1 := by
    -- a ≤ 2^a ≤ pair a b
    have hPow : a ≤ Nat.pow 2 a := le_pow_two a
    have hPow' : Nat.pow 2 a ≤ pair a b := by
      -- `2^a ≤ 2^a * (2*b+1)`
      unfold pair
      exact Nat.le_mul_of_pos_right (Nat.pow 2 a) (Nat.succ_pos (2 * b))
    have : a ≤ pair a b := le_trans hPow hPow'
    exact Nat.succ_le_succ this
  have hAux :
      unpairAux (pair a b + 1) (pair a b) = (a, 2 * b + 1) :=
    unpairAux_pair (a := a) (b := b) (fuel := pair a b + 1) hFuel
  -- unfold and take the `n = 0` false branch, then rewrite the fuel-bounded unpair.
  unfold unpair
  rw [if_neg hne]
  dsimp
  rw [hAux]
  refine Prod.ext (by rfl) ?_
  -- second component: ((2*b+1)-1)/2 = b
  have hsub : (2 * b + 1) - 1 = 2 * b := Nat.succ_sub_one (2 * b)
  rw [hsub]
  exact Nat.mul_div_right b (by decide : (0 : ℕ) < 2)

@[simp] lemma unpair_fst_pair (a b : ℕ) : unpair_fst (pair a b) = a := by
  simp [unpair_fst, unpair_pair]

@[simp] lemma unpair_snd_pair (a b : ℕ) : unpair_snd (pair a b) = b := by
  simp [unpair_snd, unpair_pair]

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
          exact Nat.not_succ_le_zero (encodeList (x :: xs)) hFuel
      | succ fuel' =>
          have hne : pair (x + 1) (encodeList xs) ≠ 0 :=
            pair_ne_zero (x + 1) (encodeList xs)
          have hFuel' : encodeList xs + 1 ≤ fuel' := by
            -- From `pair (x+1) (encodeList xs) + 1 ≤ fuel' + 1`, cancel the successor and
            -- use `encodeList xs < pair (x+1) (encodeList xs)` to pass to the tail fuel.
            have hnLe : pair (x + 1) (encodeList xs) ≤ fuel' := by
              have hnLe0 :
                  encodeList (x :: xs) ≤ fuel' :=
                (Nat.add_le_add_iff_right (m := encodeList (x :: xs)) (k := fuel') (n := 1)).1 hFuel
              simpa [encodeList] using hnLe0
            have hbLe : encodeList xs + 1 ≤ pair (x + 1) (encodeList xs) :=
              Nat.succ_le_iff.mpr
                (right_lt_pair_of_left_pos (a := x + 1) (b := encodeList xs))
            exact le_trans hbLe hnLe
          have hTail : decodeListAux fuel' (encodeList xs) = xs := ih fuel' hFuel'
          -- Unfold one step of the decoder on the encoded cons cell.
          -- We avoid `simp` here to keep the proof constructive and avoid importing
          -- simp lemmas that depend on `Classical.choice`/`Quot.sound`.
          dsimp [encodeList, decodeListAux]
          -- first `if`: `n = 0` is false
          rw [if_neg hne]
          -- second `if`: `unpair_fst (pair ...) = 0` is false since it's `x+1`
          have hx1 : unpair_fst (pair (x + 1) (encodeList xs)) = x + 1 :=
            unpair_fst_pair (x + 1) (encodeList xs)
          have hxsnd : unpair_snd (pair (x + 1) (encodeList xs)) = encodeList xs :=
            unpair_snd_pair (x + 1) (encodeList xs)
          -- reduce both unpair projections
          rw [hx1, hxsnd]
          -- `x+1 ≠ 0`
          rw [dif_neg (Nat.succ_ne_zero x)]
          -- `x+1 - 1 = x`
          rw [Nat.succ_sub_one x]
          -- apply IH on the tail
          rw [hTail]

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
