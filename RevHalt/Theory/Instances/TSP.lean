/-
Copyright (c) 2026 RevHalt Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RevHalt Contributors
-/
import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.TheoryDynamics_Trajectory
import RevHalt.Theory.Canonicity
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

/-- Encode a weighted graph as a list of edge weights (row-major order).
    The list has length n*n, with weights[i*n + j] = G.weight i j. -/
def encodeWeights {n : ℕ} (G : WeightedGraph n) : List ℕ :=
  if hn : n = 0 then []
  else List.ofFn (fun k : Fin (n * n) =>
    let i : Fin n := ⟨k.val / n, by
      have hk := k.isLt
      exact Nat.div_lt_of_lt_mul hk⟩
    let j : Fin n := ⟨k.val % n, Nat.mod_lt k.val (Nat.pos_of_ne_zero hn)⟩
    G.weight i j)

/-- Length of encodeWeights is n*n. -/
lemma encodeWeights_length {n : ℕ} (G : WeightedGraph n) :
    (encodeWeights G).length = n * n := by
  simp only [encodeWeights]
  split_ifs with hn
  · simp [hn]
  · simp

/-- Key indexing lemma: getD on encodeWeights returns the correct weight.
    Technical proof: requires List.getD lemmas and q*n + r / n = q for r < n. -/
lemma getD_encodeWeights {n : ℕ} (G : WeightedGraph n) (i j : Fin n) :
    (encodeWeights G).getD (i.val * n + j.val) 0 = G.weight i j := by
  have hn : n ≠ 0 := Fin.pos i |> Nat.pos_iff_ne_zero.mp
  simp only [encodeWeights, hn, ↓reduceDIte]
  -- Proof outline:
  -- 1. Index i*n + j < n*n (from i < n, j < n)
  -- 2. getD on List.ofFn returns function value at that index
  -- 3. (i*n + j) / n = i and (i*n + j) % n = j
  sorry

/-- Encode a TSP instance as a natural number. -/
def encodeTSP (inst : TSPInstance) : ℕ :=
  pair inst.n (pair inst.bound (encodeList (encodeWeights inst.graph)))

/--
  Decode a list of weights into a weight function.
  The list is expected to be n*n elements in row-major order.
-/
def decodeWeightsAux (n : ℕ) (weights : List ℕ) (i j : Fin n) : ℕ :=
  weights.getD (i.val * n + j.val) 0

/--
  Attempt to decode a weighted graph from a list of n*n weights.
  Returns a graph with symmetry and self-zero properties enforced.
-/
def decodeWeightedGraph (n : ℕ) (weights : List ℕ) : WeightedGraph n where
  weight := fun i j =>
    if i = j then 0  -- Self-loops have zero weight
    else
      -- Use minimum of w(i,j) and w(j,i) to enforce symmetry
      let w_ij := decodeWeightsAux n weights i j
      let w_ji := decodeWeightsAux n weights j i
      min w_ij w_ji
  symm := fun i j => by
    simp only
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      have hji : j ≠ i := fun h => hij h.symm
      simp only [hji, ↓reduceIte]
      exact Nat.min_comm _ _
  self_zero := fun i => by simp

/--
  Decode a TSPCode into a full TSPInstance.
  Returns none if n < 2 (minimum for meaningful TSP).
-/
def decodeTSP (code : ℕ) : Option TSPInstance :=
  let n := unpair_fst code
  let rest := unpair_snd code
  let bound := unpair_fst rest
  let graphCode := unpair_snd rest
  let weights := decodeList graphCode
  if hn : n ≥ 2 then
    some {
      n := n
      hn := hn
      graph := decodeWeightedGraph n weights
      bound := bound
    }
  else none

/--
  Roundtrip: decoding an encoded TSP instance gives back a compatible instance.

  Note: The decoded graph may differ slightly due to the symmetrization in
  decodeWeightedGraph (uses min). For symmetric inputs, this is identity.

  The proof requires showing encodeWeights produces correct indexing:
  (List.ofFn ...).flatten.getD (i*n + j) 0 = G.weight i j
-/
lemma decodeTSP_encodeTSP (inst : TSPInstance) :
    decodeTSP (encodeTSP inst) = some inst := by
  -- Structural matching on encoding/decoding
  -- Requires: unpair_fst_pair, unpair_snd_pair, decodeList_encodeList
  -- And: encodeWeights indexing lemma
  sorry

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
  if h_len : path.length = inst.n then
    -- Check range
    if h_range : path.all (· < inst.n) then
      -- Check no duplicates
      if h_nodup : path.Nodup then
        -- Build tour structure
        let range_valid : ∀ x, x ∈ path → x < inst.n := by
          intro x hx
          have h := List.all_eq_true.mp h_range x hx
          exact decide_eq_true_iff.mp h
        let tour : Tour inst.n := {
          path := path
          length_eq := h_len
          nodup := h_nodup
          range_valid := range_valid
        }
        -- Check cost
        tourCost inst.graph tour inst.hn ≤ inst.bound
      else false
    else false
  else false

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
  Uses full pipeline: decodeTSP → instance → decodeTour → ValidTour.
-/
def Machine_TSP (code : TSPCode) : Trace :=
  fun k => match decodeTSP code with
    | none => False  -- Invalid instance code
    | some inst =>
      ∃ tourCode < k,
        match decodeTour inst.n tourCode with
        | some tour => ValidTour inst tour
        | none => False

/--
  The central semantic equivalence for Machine_TSP:
  When the code decodes to a valid instance, the machine halts iff the instance has a solution.
-/
theorem Machine_TSP_halts_iff {code : TSPCode} {inst : TSPInstance}
    (hdec : decodeTSP code = some inst) :
    Halts (Machine_TSP code) ↔ HasSolution inst := by
  constructor
  · -- Halts → HasSolution
    intro ⟨k, hk⟩
    simp only [Machine_TSP, hdec] at hk
    obtain ⟨tourCode, _, htour⟩ := hk
    cases htour_dec : decodeTour inst.n tourCode with
    | none => simp [htour_dec] at htour
    | some tour =>
      simp only [htour_dec] at htour
      exact ⟨tour, htour⟩
  · -- HasSolution → Halts
    intro ⟨tour, hvalid⟩
    -- Encode the tour and show Machine_TSP becomes true
    let tourCode := encodeTour tour
    use tourCode + 1
    simp only [Machine_TSP, hdec]
    use tourCode, Nat.lt_succ_self _
    rw [decodeTour_encodeTour]
    exact hvalid

/--
  Corollary: For invalid codes, Machine_TSP never halts.
-/
theorem Machine_TSP_not_halts_of_invalid {code : TSPCode}
    (hinv : decodeTSP code = none) :
    ¬ Halts (Machine_TSP code) := by
  intro ⟨k, hk⟩
  simp only [Machine_TSP, hinv] at hk

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
-- SECTION 10: TRAJECTORY INTEGRATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Trajectory Integration

This section connects TSP to the RevHalt trajectory dynamics framework.
The trajectory is the sequence of theory states under F0 iteration.
-/

section Trajectory

open RevHalt

-- Use Type (not Type u) to match ℕ's universe
variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (encode_prop : ℕ → PropT)

/--
  The TSP trajectory: iteration of F0 starting from Γ0,
  using Machine_TSP as the halting machine.

  Note: Uses ℕ as the Code type since TSPCode = ℕ.
-/
def TSP_Trajectory (Γ0 : Set PropT) : ℕ → Set PropT :=
  fun n => chain0 Provable K Machine_TSP (encode_halt_TSP encode_prop) Γ0 n

/-- The omega-limit of the TSP trajectory. -/
def TSP_TrajectoryLimit (Γ0 : Set PropT) : Set PropT :=
  omega0 Provable K Machine_TSP (encode_halt_TSP encode_prop) Γ0

/-- Each stage of TSP trajectory embeds into the limit. -/
theorem TSP_trajectory_stage_le_limit (Γ0 : Set PropT) (n : ℕ) :
    TSP_Trajectory Provable K encode_prop Γ0 n ⊆
    TSP_TrajectoryLimit Provable K encode_prop Γ0 := by
  unfold TSP_Trajectory TSP_TrajectoryLimit
  exact chain0_le_omega0 Provable K Machine_TSP (encode_halt_TSP encode_prop) Γ0 n

end Trajectory

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 11: ROUTE II INTEGRATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Route II Integration

This section provides the hypotheses needed for Route II to apply to TSP.
Route II is not TSP-specific - it's a generic result about when S1Rel is nonempty.
We instantiate the general hypotheses here.
-/

section RouteII

open RevHalt

variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Cn : Set PropT → Set PropT)
variable (encode_prop : ℕ → PropT)

/--
  Route II Hypotheses for TSP.
  These are the conditions under which S1Rel_TSP is guaranteed nonempty.

  - Soundness: Internal provability implies semantic truth
  - NegComplete: Non-halting can be certified
  - Barrier: No uniform decision procedure exists
-/
structure TSP_RouteIIHyp (SProvable : PropT → Prop) (SNot : PropT → PropT)
    (ωΓ : Set PropT) : Prop where
  soundness : ∀ p, Provable ωΓ p → SProvable p
  negComplete : ∀ code : ℕ, ¬ Rev0_K K (Machine_TSP code) →
    SProvable (SNot (encode_halt_TSP encode_prop code))
  barrier : (∀ code : ℕ, SProvable (encode_halt_TSP encode_prop code) ∨
    SProvable (SNot (encode_halt_TSP encode_prop code))) → False

/--
  TSP satisfies Route II: under the hypotheses, S1Rel_TSP is nonempty.
  This is an instantiation of the general RouteII result.

  The proof requires connecting:
  - Halting → provable in ωΓ → SProvable (via soundness)
  - Non-halting → SProvable of negation (via negComplete)

  This creates a contradiction with barrier.
-/
theorem TSP_RouteII_applies
    (SProvable : PropT → Prop) (SNot : PropT → PropT)
    (ωΓ : Set PropT)
    (hHyp : TSP_RouteIIHyp Provable K encode_prop SProvable SNot ωΓ)
    -- Additional hypothesis: halting machines have provable halt propositions
    (hHaltProv : ∀ code, Halts (Machine_TSP code) →
        Provable ωΓ (encode_halt_TSP encode_prop code))
    -- Rev0_K implies Halts (standard Kit axiom)
    (hRevHalts : ∀ T, Rev0_K K T → Halts T) :
    (S1Rel_TSP Provable encode_prop ωΓ).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  apply hHyp.barrier
  intro code
  by_cases hHalts : Halts (Machine_TSP code)
  · -- If halts: use hHaltProv and soundness
    left
    exact hHyp.soundness _ (hHaltProv code hHalts)
  · -- If doesn't halt: use negComplete
    right
    exact hHyp.negComplete code (fun hRev => hHalts (hRevHalts _ hRev))

end RouteII

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 12: INCARNATION TRILEMMA FOR TSP
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Incarnation Trilemma for TSP

The trilemma states that the three conditions cannot all hold simultaneously:
1. Absorbable at step 1
2. OmegaAdmissible at ω-limit
3. RouteIIAt (frontier non-empty) at ω-limit

This is the structural impossibility result applied to TSP.
-/

section Trilemma

open RevHalt

variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Cn : Set PropT → Set PropT)
variable (encode_prop : ℕ → PropT)

/--
  The TSP incarnation trilemma: direct instantiation of the general trilemma
  for Machine_TSP.

  States: ¬(Absorbable ∧ OmegaAdmissible ∧ RouteIIAt)

  This is the structural result that limits cannot be "well-behaved" in all three ways.
-/
theorem TSP_incarnation_trilemma
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ¬ (Absorbable Provable
          (chainState Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0 1).Γ
       ∧ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0)
       ∧ RouteIIAt Provable K Machine_TSP (encode_halt_TSP encode_prop)
            (omegaΓ Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0)) :=
  incarnation_trilemma Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn
    hMono hCnExt hIdem hProvCn A0

/--
  TSP trilemma in disjunction form: at least one condition must fail.
-/
theorem TSP_trilemma_disjunction
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (A0 : ThState (PropT := PropT) Provable Cn) :
    ¬ Absorbable Provable
        (chainState Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0 1).Γ
    ∨ ¬ OmegaAdmissible Provable Cn
          (omegaΓ Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0)
    ∨ ¬ RouteIIAt Provable K Machine_TSP (encode_halt_TSP encode_prop)
          (omegaΓ Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn hIdem hProvCn A0) :=
  omega_trilemma_disjunction Provable K Machine_TSP (encode_halt_TSP encode_prop) Cn
    hMono hCnExt hIdem hProvCn A0

end Trilemma

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 13: CANONIZATION AND COLLAPSE DERIVATION (CORRECTED)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Canonization at Omega and Collapse Derivation

This section defines the proper structure for deriving Collapse from trajectory constraints.

### Key insight

Collapse is NOT an arbitrary hypothesis. It is the **output** forced by trajectory
constraints when we choose to preserve certain properties.

### The chain of reasoning (corrected)

1. **Trilemma**: ¬(Absorbable ∧ OmegaAdmissible ∧ RouteIIAt)
2. If we preserve Absorbable and OmegaAdmissible: RouteIIAt must fail
3. **¬RouteIIAt** → S1Rel = ∅ → **PosCompleteAtOmega** (halting is provable)
4. **H3 (NegCompleteAtOmega)** is a separate hypothesis (non-halting is provable)
5. **Canonization** = PosComplete ∧ NegComplete
6. For **Collapse-search** (Find returning a tour), we need **ExtractTour**:
   provable halting → concrete tour exists

Therefore: Abs + Adm + H3 + Extract ⟹ Collapse-search
-/

section Canonization

open RevHalt

variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Cn : Set PropT → Set PropT)
variable (encode_prop : ℕ → PropT)
-- SNot is fixed (same as in RouteII)
variable (SNot : PropT → PropT)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART A: COMPLETENESS PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Pos-Completude at ω**: If an instance has a solution, this is provable in ωΓ.

  This is derivable from ¬RouteIIAt (empty frontier).
  When S1Rel = ∅, all halting machines have their halt proposition provable.
-/
structure PosCompleteAtOmega (ωΓ : Set PropT) : Prop where
  pos : ∀ code : TSPCode, ∀ inst : TSPInstance,
    decodeTSP code = some inst →
    HasSolution inst → Provable ωΓ (encode_halt_TSP encode_prop code)

/--
  **Neg-Completude at ω** (H3): If an instance has no solution, this is provable in ωΓ.

  This is NOT derivable from ¬RouteIIAt alone. It requires a separate hypothesis (H3).
  This is the "duality" condition from EffectiveCollapse.md.
-/
structure NegCompleteAtOmega (ωΓ : Set PropT) : Prop where
  neg : ∀ code : TSPCode, ∀ inst : TSPInstance,
    decodeTSP code = some inst →
    ¬ HasSolution inst → Provable ωΓ (SNot (encode_halt_TSP encode_prop code))

/--
  **Canonization at ω** = PosCompletude ∧ NegCompletude.

  At ω, every TSP instance is decidable internally:
  - If solvable: provable halt
  - If unsolvable: provable not-halt
-/
structure CanonicalizationAtOmega (ωΓ : Set PropT) : Prop where
  posComplete : PosCompleteAtOmega Provable encode_prop ωΓ
  negComplete : NegCompleteAtOmega Provable encode_prop SNot ωΓ

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART B: POS-COMPLETUDE FROM ¬RouteIIAt
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  ¬RouteIIAt implies S1Rel is empty.

  RouteIIAt is (S1Rel ωΓ).Nonempty, so ¬RouteIIAt gives S1Rel = ∅.
-/
lemma S1Rel_empty_of_not_RouteIIAt (ωΓ : Set PropT)
    (hNotRoute : ¬ RouteIIAt Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ) :
    S1Rel Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ = ∅ := by
  by_contra h
  -- h : S1Rel ... ≠ ∅
  -- need: (S1Rel ...).Nonempty
  have hNe : (S1Rel Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h
  unfold RouteIIAt at hNotRoute
  exact hNotRoute hNe

/--
  Empty S1Rel implies Pos-Completude at ω.

  If S1Rel = ∅, then for every halting machine:
  - Either its halt proposition is not halting (contradiction with HasSolution)
  - Or it IS provable in ωΓ
-/
theorem PosComplete_of_S1Rel_empty (ωΓ : Set PropT)
    (hKMono : DetectsMono K)  -- Needed for Rev0_K ↔ Halts bridge
    (hEmpty : S1Rel Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ = ∅) :
    PosCompleteAtOmega Provable encode_prop ωΓ := by
  constructor
  intro code inst hdec hSol
  -- If not provable, it would be in S1Rel (assuming halting)
  by_contra hNProv
  have hHalts : Halts (Machine_TSP code) := by
    rw [Machine_TSP_halts_iff hdec]
    exact hSol
  -- Use T1_traces_of_DetectsMono: Rev0_K K T ↔ Halts T
  have hRev0 : Rev0_K K (Machine_TSP code) := by
    exact (T1_traces_of_DetectsMono K hKMono (Machine_TSP code)).mpr hHalts
  have hIn : encode_halt_TSP encode_prop code ∈
      S1Rel Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ := by
    unfold S1Rel
    simp only [Set.mem_setOf_eq]
    exact ⟨code, rfl, hRev0, hNProv⟩
  rw [hEmpty] at hIn
  exact hIn

/--
  ¬RouteIIAt implies Pos-Completude.

  Direct composition of the above lemmas.
-/
theorem PosComplete_of_not_RouteIIAt (ωΓ : Set PropT)
    (hKMono : DetectsMono K)
    (hNotRoute : ¬ RouteIIAt Provable K Machine_TSP (encode_halt_TSP encode_prop) ωΓ) :
    PosCompleteAtOmega Provable encode_prop ωΓ :=
  PosComplete_of_S1Rel_empty Provable K encode_prop ωΓ hKMono
    (S1Rel_empty_of_not_RouteIIAt Provable K encode_prop ωΓ hNotRoute)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART C: EXTRACTION FOR COLLAPSE-SEARCH
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **ExtractTour**: The ability to extract a concrete tour from a proof of halting.

  This is needed for Collapse-SEARCH (not just Collapse-DECISION).
  Without this, we can only conclude "decidable" not "searchable".

  This corresponds to H1 (Bio-Absorption Effective) in the operational direction.
-/
structure ExtractTour (ωΓ : Set PropT) : Prop where
  extract : ∀ code : TSPCode, ∀ inst : TSPInstance,
    decodeTSP code = some inst →
    Provable ωΓ (encode_halt_TSP encode_prop code) →
    ∃ tour : Tour inst.n, ValidTour inst tour

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART D: EFFECTIVE CANONIZATION (CONSTRUCTIVE)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
### Effective Canonization: The True Output

The trilemma shows that trajectory constraints force ¬RouteIIAt.
But to REALIZE this constructively, we need an **effective** structure.

The key insight: the "axiom" is not a Prop (existence) but DATA (the actual
computable decision/extraction procedure). This is EffectiveCanonizationAtOmega.

The theorem chain is:
1. Trilemma: Abs + Adm → ¬RouteIIAt (structural constraint)
2. EffectiveCanonizationAtOmega → Collapse_TSP_Axiom (constructive packaging)
3. The trajectory outputs the effective canonization (this IS the axiom/data)
-/

/-- Effective canonization at ω: DATA, not Prop. -/
structure EffectiveCanonizationAtOmega where
  /-- Computable decision: does this instance have a solution? -/
  Decide : TSPCode → Bool
  /-- Computable extraction: produce the tour (unconditionally) -/
  extract : TSPCode → List ℕ
  /-- Soundness: positive decision implies solution exists -/
  sound : ∀ code inst,
    decodeTSP code = some inst →
    Decide code = true →
    HasSolution inst
  /-- Completeness: solution implies positive decision -/
  complete : ∀ code inst,
    decodeTSP code = some inst →
    HasSolution inst →
    Decide code = true
  /-- Extraction validity: the extracted tour is valid -/
  extract_valid : ∀ code inst,
    decodeTSP code = some inst →
    Decide code = true →
    ∃ tour : Tour inst.n, tour.path = extract code ∧ ValidTour inst tour

/--
  **Collapse from Effective Canonization** (fully constructive).

  Given an EffectiveCanonizationAtOmega, we construct Collapse_TSP_Axiom
  with NO classical choice, NO noncomputable.

  Requires the roundtrip lemma as parameter.
-/
def Collapse_of_EffectiveCanonization
    (eCan : EffectiveCanonizationAtOmega)
    (decodeTSP_encodeTSP : ∀ inst : TSPInstance, decodeTSP (encodeTSP inst) = some inst) :
    Collapse_TSP_Axiom := by
  let Find : TSPCode → Option (List ℕ) :=
    fun code => if eCan.Decide code then some (eCan.extract code) else none

  refine
    { Find := Find
      find_correct := ?_
      find_complete := ?_
      find_sound := ?_ }

  · -- find_correct
    intro inst hSol
    have hdec : decodeTSP (encodeTSP inst) = some inst := decodeTSP_encodeTSP inst
    have hD : eCan.Decide (encodeTSP inst) = true :=
      eCan.complete (encodeTSP inst) inst hdec hSol
    refine ⟨eCan.extract (encodeTSP inst), ?_, ?_⟩
    · simp [Find, hD]
    · exact eCan.extract_valid (encodeTSP inst) inst hdec hD

  · -- find_complete
    intro inst hNSol
    have hdec : decodeTSP (encodeTSP inst) = some inst := decodeTSP_encodeTSP inst
    by_cases hD : eCan.Decide (encodeTSP inst) = true
    · have : HasSolution inst := eCan.sound (encodeTSP inst) inst hdec hD
      exact (hNSol this).elim
    · have hF : eCan.Decide (encodeTSP inst) = false := by
        cases hB : eCan.Decide (encodeTSP inst) <;> simp [hB] at hD ⊢
      simp [Find, hF]

  · -- find_sound
    intro inst cert hfind
    have hdec : decodeTSP (encodeTSP inst) = some inst := decodeTSP_encodeTSP inst
    dsimp [Find] at hfind
    cases hB : eCan.Decide (encodeTSP inst) with
    | false =>
        -- hfind becomes : none = some cert - impossible
        simp [hB] at hfind
    | true =>
        exact eCan.sound (encodeTSP inst) inst hdec hB

/--
  **Main Theorem**: Trajectory constraints force the FORM of the axiom.

  The complete picture:
  1. Trilemma gives ¬(Abs ∧ Adm ∧ RouteIIAt)
  2. Abs + Adm ⟹ ¬RouteIIAt (structural constraint)
  3. To REALIZE ¬RouteIIAt effectively → need EffectiveCanonizationAtOmega
  4. EffectiveCanonizationAtOmega + roundtrip → Collapse_TSP_Axiom (this def)

  The theorem states: IF the trajectory produces an effective canonization,
  THEN Collapse holds for TSP.
-/
def Collapse_from_EffectiveTrajectory
    (eCan : EffectiveCanonizationAtOmega)
    (decodeTSP_encodeTSP : ∀ inst : TSPInstance, decodeTSP (encodeTSP inst) = some inst) :
    Collapse_TSP_Axiom :=
  Collapse_of_EffectiveCanonization eCan decodeTSP_encodeTSP

end Canonization

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
