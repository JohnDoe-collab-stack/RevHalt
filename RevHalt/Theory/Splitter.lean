import Mathlib.Data.List.Basic
import Mathlib.Tactic.GCongr

/-!
# RevHalt.Theory.Splitter

Abstract finite observation framework: Splitters, Atomicity, Residue, Queue.

## Contents
- `Splitter` structure with Refinement and Cover axioms
- Composition and atomicity
- `Prime_RH` as atomic index
- `ResEquiv` (residue equivalence at depth d)
- `Queue` (persistent residue under dynamics)
-/

namespace RevHalt.Splitter

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Core Types
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Pos : Type)

/-- A constraint is a predicate on positions. -/
abbrev Constraint := Pos → Prop

/-- Information state: a list of constraints (finite bundle). -/
abbrev Info := List (Pos → Prop)

/-- Position n satisfies information state I. -/
def Sat (I : Info Pos) (n : Pos) : Prop := ∀ c ∈ I, c n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Splitter Interface
-- ═══════════════════════════════════════════════════════════════════════════════

set_option linter.dupNamespace false
/-- A Splitter is a finite cover operator on information states. -/
structure Splitter where
  /-- Split produces a finite list of refined information states. -/
  split : Info Pos → List (Info Pos)

  /-- Refinement: each case only adds information. -/
  refinement : ∀ I J, J ∈ split I → (∀ n, Sat Pos J n → Sat Pos I n)

  /-- Cover: every compatible position falls into at least one case. -/
  cover : ∀ I n, Sat Pos I n → ∃ J ∈ split I, Sat Pos J n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Composition
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Compose two splitters: first A, then B on each case. -/
def compose (A B : Splitter Pos) : Splitter Pos where
  split I := (A.split I).flatMap B.split
  refinement := by
    intro I J hJ
    have hMem : ∃ K, K ∈ A.split I ∧ J ∈ B.split K := List.mem_flatMap.mp hJ
    obtain ⟨K, hK_in_A, hJ_in_B⟩ := hMem
    intro n hSatJ
    apply A.refinement I K hK_in_A
    apply B.refinement K J hJ_in_B
    exact hSatJ
  cover := by
    intro I n hSatI
    obtain ⟨K, hK_in_A, hSatK⟩ := A.cover I n hSatI
    obtain ⟨J, hJ_in_B, hSatJ⟩ := B.cover K n hSatK
    refine ⟨J, ?_, hSatJ⟩
    exact List.mem_flatMap.mpr ⟨K, hK_in_A, hJ_in_B⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3.5) Equivalence
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two splitters are equivalent if they induce the same satisfiability structure at depth 1. -/
def SplitterEquiv (A B : Splitter Pos) : Prop :=
  ∀ I n m,
    (∃ J ∈ A.split I, Sat Pos J n ∧ Sat Pos J m) ↔
    (∃ K ∈ B.split I, Sat Pos K n ∧ Sat Pos K m)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Trivial and Atomic
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A splitter is trivial if it never really distinguishes anything. -/
def isTrivial (S : Splitter Pos) : Prop :=
  ∀ I, ∀ J ∈ S.split I, (∀ n, Sat Pos I n ↔ Sat Pos J n)

/-- A splitter is nontrivial if there exists a case that distinguishes. -/
def isNontrivial (S : Splitter Pos) : Prop := ¬ isTrivial Pos S

/-- A splitter is atomic relative to an admissible class if it is Irreducible.
    i.e., if S ~ A ∘ B with A,B nontrivial, then A ~ S or B ~ S.
    (This allows S ∘ S ~ S for idempotent splitters like Mod p). -/
def isAtomicRelative (S : Splitter Pos) (Adm : Splitter Pos → Prop) : Prop :=
  isNontrivial Pos S ∧
  Adm S ∧
  ∀ A B : Splitter Pos, Adm A → Adm B → isNontrivial Pos A → isNontrivial Pos B →
    SplitterEquiv Pos (compose Pos A B) S →
    (SplitterEquiv Pos A S ∨ SplitterEquiv Pos B S)

/-- A splitter is atomic (absolute) if atomic relative to all splitters. -/
def isAtomic (S : Splitter Pos) : Prop := isAtomicRelative Pos S (fun _ => True)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Prime as Atomic Index
-- ═══════════════════════════════════════════════════════════════════════════════

variable (SplitFamily : ℕ → Splitter ℕ)
variable (Adm : Splitter ℕ → Prop)

/-- Prime_RH(p) holds iff Split_p is atomic in Adm. -/
def Prime_RH (p : ℕ) : Prop := isAtomicRelative ℕ (SplitFamily p) Adm

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Depth-Bounded Cases
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cases reachable at depth d from initial info I. -/
def Cases (S : Splitter Pos) : ℕ → Info Pos → List (Info Pos)
  | 0, I => [I]
  | d + 1, I => (Cases S d I).flatMap S.split

/-- Size bound lemmas. -/
theorem length_flatMap_eq_sum {α β} (l : List α) (f : α → List β) :
    (l.flatMap f).length = (l.map (fun x => (f x).length)).sum := by
  simp [List.length_flatMap]

/-- Sum of mapped values is bounded by length * max. -/
theorem sum_map_le_length_mul {α} (l : List α) (f : α → ℕ) (k : ℕ) (h : ∀ x ∈ l, f x ≤ k) :
    (l.map f).sum ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map, List.sum_cons, List.length_cons]
    have h1 : f head ≤ k := h head (by simp)
    have h2 : (tail.map f).sum ≤ tail.length * k := ih (fun x hx => h x (List.mem_cons_of_mem head hx))
    have goal : f head + (tail.map f).sum ≤ (tail.length + 1) * k := by
      calc f head + (tail.map f).sum
          ≤ k + tail.length * k := Nat.add_le_add h1 h2
        _ = k + k * tail.length := by rw [Nat.mul_comm tail.length k]
        _ = k * 1 + k * tail.length := by rw [Nat.mul_one]
        _ = k * (1 + tail.length) := by rw [Nat.mul_add]
        _ = k * (tail.length + 1) := by rw [Nat.add_comm 1]
        _ = (tail.length + 1) * k := by rw [Nat.mul_comm]
    exact goal

theorem cases_card_bound (S : Splitter Pos) (k : ℕ)
    (hk : ∀ I, (S.split I).length ≤ k) :
    ∀ d I, (Cases Pos S d I).length ≤ k ^ d := by
  intro d I
  induction d generalizing I with
  | zero =>
    simp [Cases]
  | succ d ih =>
    simp only [Cases]
    rw [length_flatMap_eq_sum]
    have h1 : ((Cases Pos S d I).map (fun x => (S.split x).length)).sum ≤ (Cases Pos S d I).length * k := by
      apply sum_map_le_length_mul
      intro x _
      exact hk x
    have h2 : (Cases Pos S d I).length ≤ k ^ d := ih I
    calc ((Cases Pos S d I).map (fun x => (S.split x).length)).sum
        ≤ (Cases Pos S d I).length * k := h1
      _ ≤ k ^ d * k := Nat.mul_le_mul_right k h2
      _ = k ^ (d + 1) := (Nat.pow_succ k d).symm

/-- Cases Cover Property: Every position satisfying I is covered by some case in Cases(d, I). -/
theorem cases_cover (S : Splitter Pos) (d : ℕ) (I : Info Pos) (n : Pos)
    (hSat : Sat Pos I n) :
    ∃ J ∈ Cases Pos S d I, Sat Pos J n := by
  induction d generalizing I with
  | zero =>
    use I
    simp [Cases, hSat]
  | succ d ih =>
    simp only [Cases, List.mem_flatMap]
    -- Cases(d+1, I) = Cases(d, I).flatMap S.split
    -- So we first apply IH to get J' in Cases(d, I) covering n.
    obtain ⟨J', hJ'_in_Cases, hSatJ'⟩ := ih I hSat
    -- Then apply S.cover on J' to get K in S.split(J') covering n.
    obtain ⟨K, hK_in_splitJ', hSatK⟩ := S.cover J' n hSatJ'
    -- K is the target.
    exact ⟨K, ⟨J', hJ'_in_Cases, hK_in_splitJ'⟩, hSatK⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Residue Equivalence
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two positions are residue-equivalent at depth d if no case distinguishes them. -/
def ResEquiv (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n m : Pos) : Prop :=
  ∀ J ∈ Cases Pos S d I0, (Sat Pos J n ↔ Sat Pos J m)

/-- ResEquiv is reflexive. -/
theorem resEquiv_refl (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n : Pos) :
    ResEquiv Pos S d I0 n n := fun _ _ => Iff.rfl

/-- ResEquiv is symmetric. -/
theorem resEquiv_symm (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n m : Pos) :
    ResEquiv Pos S d I0 n m → ResEquiv Pos S d I0 m n :=
  fun h J hJ => (h J hJ).symm

/-- ResEquiv is transitive. -/
theorem resEquiv_trans (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n m k : Pos) :
    ResEquiv Pos S d I0 n m → ResEquiv Pos S d I0 m k → ResEquiv Pos S d I0 n k :=
  fun hnm hmk J hJ => (hnm J hJ).trans (hmk J hJ)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Queue: Persistent Residue Under Dynamics
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Next : Pos → Pos)

/-- Iterate Next t times. -/
def iterate (t : ℕ) (n : Pos) : Pos :=
  match t with
  | 0 => n
  | t + 1 => Next (iterate t n)

/-- Queue(d, n) holds iff residue is invariant along the orbit of n. -/
def Queue (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n : Pos) : Prop :=
  ∀ t : ℕ, ResEquiv Pos S d I0 n (iterate Pos Next t n)

/-- Additive property of iterate. -/
theorem iterate_add (t s : ℕ) (n : Pos) :
    iterate Pos Next (t + s) n = iterate Pos Next s (iterate Pos Next t n) := by
  induction s with
  | zero => simp [iterate]
  | succ s ih => simp [iterate, ih]

/-- Queue is closed under dynamics (orbit stability). -/
theorem queue_orbit_closed (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n : Pos)
    (hQ : Queue Pos Next S d I0 n) (t : ℕ) :
    Queue Pos Next S d I0 (iterate Pos Next t n) := by
  intro s
  -- Transitivity: n ~ (t+s) and n ~ t implies t ~ (t+s)
  -- Symm: n ~ t -> t ~ n
  have h_tn : ResEquiv Pos S d I0 (iterate Pos Next t n) n :=
    resEquiv_symm Pos S d I0 n (iterate Pos Next t n) (hQ t)
  have h_n_ts : ResEquiv Pos S d I0 n (iterate Pos Next (t + s) n) :=
    hQ (t + s)

  -- Rewrite (t+s) to s + t (composition)
  rw [iterate_add Pos Next t s n] at h_n_ts

  -- Composition: t ~ n ~ (s after t)
  apply resEquiv_trans Pos S d I0 (iterate Pos Next t n) n
  · exact h_tn
  · exact h_n_ts

end RevHalt.Splitter

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Splitter.compose
#print axioms RevHalt.Splitter.isAtomic
#print axioms RevHalt.Splitter.Prime_RH
#print axioms RevHalt.Splitter.Cases
#print axioms RevHalt.Splitter.ResEquiv
#print axioms RevHalt.Splitter.Queue
