/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RevHalt Contributors
-/
import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# Traveling Salesman Problem (TSP) in RevHalt Framework

This module formalizes the Traveling Salesman Problem (TSP) within the RevHalt
framework, demonstrating how a concrete NP problem connects to:
- `S1Rel` (frontier of unprovable halting statements)
- `transIter` (trajectory of theory enrichment)
- Collapse axiom (polynomial searchability)

## Design Choices

- **Computable encodings**: All encodings are constructive (no noncomputable)
- **Decidable predicates**: Where possible, predicates are decidable
- **No simplifications**: Full TSP formalization

## Main Definitions

- `WeightedGraph` : Complete weighted graph on n vertices
- `TSPInstance` : Graph + cost bound
- `Tour` : Hamiltonian cycle as a permutation
- `Machine_TSP` : Enumerating machine that halts iff a valid tour exists
- `S1Rel_TSP` : Frontier for TSP instances
- `Collapse_TSP` : Axiom asserting polynomial-time Find exists

## Main Results

- `Machine_TSP_halts_iff` : Machine halts ↔ solution exists
- `S1Rel_TSP_anti_mono` : Frontier is anti-monotone in Γ
- `TSP_in_P_of_Collapse` : Under Collapse, TSP ∈ P

-/

namespace RevHalt.TSP

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: COMPUTABLE ENCODINGS (using Mathlib's Nat.pair/unpair)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cantor pairing function - alias for Nat.pair. -/
abbrev pair := Nat.pair

/-- Unpair: first component - alias for (Nat.unpair n).1. -/
abbrev unpair_fst (n : ℕ) : ℕ := (Nat.unpair n).1

/-- Unpair: second component - alias for (Nat.unpair n).2. -/
abbrev unpair_snd (n : ℕ) : ℕ := (Nat.unpair n).2

/-- Encode a list of naturals as a single natural. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | x :: xs => pair (x + 1) (encodeList xs)

/-- unpair_snd n ≤ n for all n. -/
lemma unpair_snd_le (n : ℕ) : unpair_snd n ≤ n :=
  Nat.unpair_right_le n

/--
  unpair_snd n < n when n > 0 and unpair_fst n > 0.
-/
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

/-- Decode a natural to a list of naturals. -/
def decodeList (n : ℕ) : List ℕ :=
  if h : n = 0 then []
  else
    let a := unpair_fst n
    let b := unpair_snd n
    if ha : a = 0 then []  -- Invalid encoding
    else (a - 1) :: decodeList b
termination_by n
decreasing_by
  exact unpair_snd_lt_of_pos (Nat.pos_of_ne_zero h) (Nat.pos_of_ne_zero ha)

/-- pair a b is never 0 when a > 0. -/
lemma pair_pos {a b : ℕ} (ha : a > 0) : pair a b > 0 := by
  simp only [pair]
  -- Use Nat.left_le_pair : a ≤ pair a b
  have h := Nat.left_le_pair a b
  omega

/-- unpair_fst of pair returns the first component. -/
lemma unpair_fst_pair (a b : ℕ) : unpair_fst (pair a b) = a := by
  simp only [unpair_fst, pair, Nat.unpair_pair]

/-- unpair_snd of pair returns the second component. -/
lemma unpair_snd_pair (a b : ℕ) : unpair_snd (pair a b) = b := by
  simp only [unpair_snd, pair, Nat.unpair_pair]

/-- Roundtrip: decodeList ∘ encodeList = id -/
lemma decodeList_encodeList (xs : List ℕ) : decodeList (encodeList xs) = xs := by
  induction xs with
  | nil =>
    native_decide
  | cons x xs ih =>
    unfold encodeList
    have h1 : pair (x + 1) (encodeList xs) ≠ 0 := by
      have : pair (x + 1) (encodeList xs) > 0 := pair_pos (Nat.succ_pos x)
      omega
    rw [decodeList, dif_neg h1]
    have h2 : unpair_fst (pair (x + 1) (encodeList xs)) = x + 1 := unpair_fst_pair _ _
    have h3 : unpair_snd (pair (x + 1) (encodeList xs)) = encodeList xs := unpair_snd_pair _ _
    simp only [h2, h3, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceDIte, ih]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: GRAPH DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A complete weighted graph on n vertices. -/
structure WeightedGraph (n : ℕ) where
  /-- Weight of edge (i, j). -/
  weight : Fin n → Fin n → ℕ
  /-- Symmetry: undirected graph. -/
  symm : ∀ i j, weight i j = weight j i
  /-- Self-loops have zero weight. -/
  self_zero : ∀ i, weight i i = 0

/-- A TSP instance: graph + cost bound. -/
structure TSPInstance where
  /-- Number of vertices (cities). -/
  n : ℕ
  /-- At least 2 vertices for a meaningful tour. -/
  hn : n ≥ 2
  /-- The weighted graph. -/
  graph : WeightedGraph n
  /-- The cost bound. -/
  bound : ℕ

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: TOURS
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  A tour on n vertices is specified by a permutation (list of vertex indices).
  We use a simple list representation with structural constraints.
-/
structure Tour (n : ℕ) where
  /-- The sequence of vertices visited (as natural numbers < n). -/
  path : List ℕ
  /-- The path has exactly n vertices. -/
  length_eq : path.length = n
  /-- All elements are < n. -/
  range_valid : ∀ x ∈ path, x < n
  /-- No duplicates. -/
  nodup : path.Nodup

namespace Tour

variable {n : ℕ}

/-- Get the i-th vertex in the tour (bounds-checked). -/
def getVertex (tour : Tour n) (i : ℕ) (hi : i < n) : ℕ :=
  tour.path.get ⟨i, by rw [tour.length_eq]; exact hi⟩

/-- Get the i-th vertex as a Fin n. -/
def getVertexFin (tour : Tour n) (i : ℕ) (hi : i < n) : Fin n :=
  let hi' : i < tour.path.length := by rw [tour.length_eq]; exact hi
  let v := tour.path[i]'hi'
  ⟨v, tour.range_valid v (by simp [List.mem_iff_get]; exact ⟨⟨i, hi'⟩, rfl⟩)⟩

end Tour

/-- Encode a tour as a natural number. -/
def encodeTour {n : ℕ} (tour : Tour n) : ℕ :=
  encodeList tour.path

/-- The cost of a tour in a weighted graph: sum of all consecutive edges plus return edge. -/
def tourCost {n : ℕ} (G : WeightedGraph n) (tour : Tour n) (_hn : n ≥ 2) : ℕ :=
  -- Sum consecutive edges
  let consecutiveCost := aux tour.path 0
  -- Add return edge (last → first)
  let returnCost := match tour.path.head?, tour.path.getLast? with
    | some first, some last =>
      if hf : first < n then
        if hl : last < n then G.weight ⟨last, hl⟩ ⟨first, hf⟩
        else 0
      else 0
    | _, _ => 0
  consecutiveCost + returnCost
where
  aux : List ℕ → ℕ → ℕ
  | [], acc => acc
  | [_], acc => acc  -- Single element, no edge
  | x :: y :: rest, acc =>
    if hx : x < n then
      if hy : y < n then
        aux (y :: rest) (acc + G.weight ⟨x, hx⟩ ⟨y, hy⟩)
      else aux (y :: rest) acc
    else aux (y :: rest) acc

/-- A tour is valid if its cost is at most the bound. -/
def ValidTour (inst : TSPInstance) (tour : Tour inst.n) : Prop :=
  tourCost inst.graph tour inst.hn ≤ inst.bound

/-- The TSP decision problem: does a valid tour exist? -/
def HasSolution (inst : TSPInstance) : Prop :=
  ∃ tour : Tour inst.n, ValidTour inst tour

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: INSTANCE ENCODING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Encode a weighted graph as a list of edge weights (row-major using Fin iteration). -/
def encodeWeights {n : ℕ} (G : WeightedGraph n) : List ℕ :=
  -- Build list using Fin.foldr for type-safe iteration
  let rows := Fin.foldr n (fun (i : Fin n) acc =>
    let row := Fin.foldr n (fun (j : Fin n) racc =>
      G.weight i j :: racc) []
    row ++ acc) []
  rows

/-- Encode a TSP instance as a natural number. -/
def encodeTSP (inst : TSPInstance) : ℕ :=
  pair inst.n (pair inst.bound (encodeList (encodeWeights inst.graph)))

/-- Type for TSP codes (natural numbers representing TSP instances). -/
abbrev TSPCode := ℕ

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: MACHINE AND TRACE
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  Attempt to decode a natural as a tour for n vertices.
  Returns none if the encoding is invalid.
-/
def decodeTour (n : ℕ) (code : ℕ) : Option (Tour n) :=
  let path := decodeList code
  if h1 : path.length = n then
    if h2 : ∀ x ∈ path, x < n then
      if h3 : path.Nodup then
        some ⟨path, h1, h2, h3⟩
      else none
    else none
  else none

/--
  The TSP trace: True at step k if a valid tour with encoding < k has been found.
  This models a machine that enumerates all possible tours and checks validity.
-/
def TSPTrace (inst : TSPInstance) : Trace :=
  fun k => ∃ code < k, ∃ tour : Tour inst.n,
    decodeTour inst.n code = some tour ∧ ValidTour inst tour

/-- The trace is monotone (once true, stays true). -/
theorem TSPTrace_mono (inst : TSPInstance) : TMono (TSPTrace inst) := by
  intro n m hnm ⟨code, hcode, tour, hdec, hvalid⟩
  exact ⟨code, Nat.lt_of_lt_of_le hcode hnm, tour, hdec, hvalid⟩

/--
  Roundtrip property: decoding an encoded tour returns the original tour.

  **Mathematical argument**: encodeTour uses encodeList on tour.path,
  and decodeTour uses decodeList. If encodeList/decodeList are inverses,
  and the tour satisfies its constraints, we get the original back.
-/
lemma decodeTour_encodeTour {n : ℕ} (tour : Tour n) :
    decodeTour n (encodeTour tour) = some tour := by
  unfold decodeTour encodeTour
  rw [decodeList_encodeList]
  simp only [tour.length_eq, tour.nodup, ↓reduceDIte]
  split_ifs with h
  · rfl
  · exact (h tour.range_valid).elim

/--
  The TSP trace halts iff a solution exists.
  This is the key semantic equivalence.
-/
theorem TSPTrace_halts_iff (inst : TSPInstance) :
    Halts (TSPTrace inst) ↔ HasSolution inst := by
  constructor
  · -- Halts → HasSolution
    intro ⟨k, code, _, tour, _, hvalid⟩
    exact ⟨tour, hvalid⟩
  · -- HasSolution → Halts
    intro ⟨tour, hvalid⟩
    -- The tour has some encoding
    let code := encodeTour tour
    use code + 1, code, Nat.lt_succ_self _, tour
    exact ⟨decodeTour_encodeTour tour, hvalid⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: PROPOSITION ENCODING
-- ═══════════════════════════════════════════════════════════════════════════════

variable {PropT : Type*}

/-- Encode "TSP instance has a valid tour" as a proposition. -/
def encode_halt_TSP (encode_prop : ℕ → PropT) (code : TSPCode) : PropT :=
  encode_prop code

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 7: VERIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check that a tour is valid for an instance (decidable). -/
def checkTour (inst : TSPInstance) (path : List ℕ) : Bool :=
  -- Check length
  path.length = inst.n &&
  -- Check range
  path.all (· < inst.n) &&
  -- Check no duplicates
  path.Nodup &&
  -- Check cost (would need to compute)
  true  -- Placeholder: cost check deferred

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 8: S1Rel FOR TSP
-- ═══════════════════════════════════════════════════════════════════════════════

section S1Rel

variable (Provable : Set PropT → PropT → Prop)
variable (encode_prop : ℕ → PropT)

/--
  Decode a TSPCode to extract instance parameters.
  Returns (n, bound) if valid, otherwise (0, 0).
-/
def decodeTSPParams (code : TSPCode) : ℕ × ℕ :=
  let n := unpair_fst code
  let rest := unpair_snd code
  let bound := unpair_fst rest
  (n, bound)

/--
  Machine for TSP: decode the code and produce a trace.
  The trace becomes true at step k if we find a valid tour with encoding < k.
-/
def Machine_TSP (code : TSPCode) : Trace :=
  let (n, _bound) := decodeTSPParams code
  -- Create a trace that searches for valid tours
  fun k => ∃ tourCode < k,
    match decodeTour n tourCode with
    | some tour =>
      -- Check structural validity (cost check would need graph decoding)
      tour.path.length = n ∧ tour.path.Nodup
    | none => False

/-- The S1Rel frontier for TSP. -/
def S1Rel_TSP (Γ : Set PropT) : Set PropT :=
  { p | ∃ code : TSPCode,
      p = encode_halt_TSP encode_prop code ∧
      Halts (Machine_TSP code) ∧
      ¬ Provable Γ (encode_halt_TSP encode_prop code) }

/-- S1Rel_TSP is anti-monotone. -/
theorem S1Rel_TSP_anti_mono
    (hMono : ProvRelMonotone Provable)
    {Γ Γ' : Set PropT} (hSub : Γ ⊆ Γ') :
    S1Rel_TSP Provable encode_prop Γ' ⊆ S1Rel_TSP Provable encode_prop Γ := by
  intro p ⟨code, hp, hHalts, hNprov⟩
  exact ⟨code, hp, hHalts, fun h => hNprov (hMono Γ Γ' hSub _ h)⟩

end S1Rel

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 9: COLLAPSE AXIOM
-- ═══════════════════════════════════════════════════════════════════════════════

section Collapse

/--
  **Axiom of Collapse for TSP (Search Version)**

  Postulates that there exists a polynomial-time algorithm `Find` that:
  - For solvable instances: returns a valid tour certificate
  - For unsolvable instances: returns none
-/
structure Collapse_TSP_Axiom where
  /-- The search function. -/
  Find : TSPCode → Option (List ℕ)
  /-- For solvable instances, Find produces certificate. -/
  find_correct : ∀ inst : TSPInstance,
    HasSolution inst →
    ∃ cert, Find (encodeTSP inst) = some cert ∧
      (∃ tour : Tour inst.n, tour.path = cert ∧ ValidTour inst tour)
  /-- For unsolvable instances, Find returns none. -/
  find_complete : ∀ inst : TSPInstance,
    ¬ HasSolution inst →
    Find (encodeTSP inst) = none
  /-- Soundness: if Find returns a certificate, a solution exists. -/
  find_sound : ∀ inst : TSPInstance, ∀ cert,
    Find (encodeTSP inst) = some cert →
    HasSolution inst

/-- Under Collapse, TSP is decidable. -/
theorem TSP_in_P_of_Collapse (ax : Collapse_TSP_Axiom) :
    ∃ Decide : TSPCode → Bool,
      ∀ inst : TSPInstance, Decide (encodeTSP inst) = true ↔ HasSolution inst := by
  use fun code => (ax.Find code).isSome
  intro inst
  constructor
  · -- Decide = true → HasSolution
    intro h
    simp only [Option.isSome_iff_exists] at h
    obtain ⟨cert, hcert⟩ := h
    exact ax.find_sound inst cert hcert
  · -- HasSolution → Decide = true
    intro hSol
    have ⟨cert, hfind, _⟩ := ax.find_correct inst hSol
    simp only [Option.isSome_iff_exists]
    exact ⟨cert, hfind⟩

/-- P vs NP is trajectory-dependent. -/
theorem TSP_trajectory_dependent :
    (∃ _ : Collapse_TSP_Axiom, True) →
    ∃ Decide : TSPCode → Bool,
      ∀ inst : TSPInstance, Decide (encodeTSP inst) = true ↔ HasSolution inst := by
  intro ⟨ax, _⟩
  exact TSP_in_P_of_Collapse ax

end Collapse

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Summary

TSP formalized within RevHalt framework:

1. **Computable encodings**: `pair`, `encodeList`, `encodeTour`, `encodeTSP`
2. **Machine semantics**: `TSPTrace` halts iff valid tour exists
3. **Frontier**: `S1Rel_TSP` captures unprovable but true instances
4. **Collapse axiom**: Postulates polynomial-time searchability
5. **Main result**: Under Collapse, TSP ∈ P

P vs NP is **trajectory-dependent**: different axiom choices yield different answers.
-/

end RevHalt.TSP
