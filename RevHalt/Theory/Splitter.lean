import Mathlib.Data.List.Basic

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
-- 4) Trivial and Atomic
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A splitter is trivial if it never really distinguishes anything. -/
def isTrivial (S : Splitter Pos) : Prop :=
  ∀ I, ∀ J ∈ S.split I, (∀ n, Sat Pos I n ↔ Sat Pos J n)

/-- A splitter is nontrivial if there exists a case that distinguishes. -/
def isNontrivial (S : Splitter Pos) : Prop := ¬ isTrivial Pos S

/-- A splitter is atomic if nontrivial and not factorisable. -/
def isAtomic (S : Splitter Pos) : Prop :=
  isNontrivial Pos S ∧
  ∀ A B : Splitter Pos, isNontrivial Pos A → isNontrivial Pos B →
    compose Pos A B ≠ S

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Prime as Atomic Index
-- ═══════════════════════════════════════════════════════════════════════════════

variable (SplitFamily : ℕ → Splitter ℕ)

/-- Prime_RH(p) holds iff Split_p is atomic. -/
def Prime_RH (p : ℕ) : Prop := isAtomic ℕ (SplitFamily p)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Depth-Bounded Cases
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cases reachable at depth d from initial info I. -/
def Cases (S : Splitter Pos) : ℕ → Info Pos → List (Info Pos)
  | 0, I => [I]
  | d + 1, I => (Cases S d I).flatMap S.split

/-- Size bound (stated, proof uses arithmetic lemmas). -/
theorem cases_card_bound (S : Splitter Pos) (k : ℕ)
    (hk : ∀ I, (S.split I).length ≤ k) :
    ∀ d I, (Cases Pos S d I).length ≤ k ^ d := by
  sorry

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
