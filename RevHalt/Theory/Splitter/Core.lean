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
-- 3.5) Equivalence (Shallow: depth 1)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two splitters are equivalent at depth 1 if they induce the same satisfiability structure. -/
def SplitterEquiv (A B : Splitter Pos) : Prop :=
  ∀ I n m,
    (∃ J ∈ A.split I, Sat Pos J n ∧ Sat Pos J m) ↔
    (∃ K ∈ B.split I, Sat Pos K n ∧ Sat Pos K m)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3.6) Identity Splitter
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The identity splitter: Split(I) = {I}. -/
def IdSplitter : Splitter Pos where
  split I := [I]
  refinement := by
    intro I J hJ n hSatJ
    simp only [List.mem_singleton] at hJ
    subst hJ
    exact hSatJ
  cover := by
    intro I n hSatI
    use I
    simp only [List.mem_singleton, true_and]
    exact hSatI

/-- Id ⊗ S ≈ S (left identity). -/
theorem id_compose_left (S : Splitter Pos) : SplitterEquiv Pos (compose Pos (IdSplitter Pos) S) S := by
  intro I n m
  have h : (compose Pos (IdSplitter Pos) S).split I = S.split I := by
    simp only [compose, IdSplitter, List.flatMap, List.map, List.flatten]
    exact List.append_nil _
  simp only [h]

/-- S ⊗ Id ≈ S (right identity). -/
theorem id_compose_right (S : Splitter Pos) : SplitterEquiv Pos (compose Pos S (IdSplitter Pos)) S := by
  intro I n m
  constructor
  · intro ⟨J, hJ, hSat⟩
    simp only [compose, IdSplitter, List.mem_flatMap, List.mem_singleton] at hJ
    obtain ⟨K, hK_in, hJ_eq⟩ := hJ
    use K
    exact ⟨hK_in, by rw [← hJ_eq]; exact hSat⟩
  · intro ⟨J, hJ, hSat⟩
    use J
    simp only [compose, IdSplitter, List.mem_flatMap, List.mem_singleton]
    exact ⟨⟨J, hJ, rfl⟩, hSat⟩

/-- Composition is associative: (A ⊗ B) ⊗ C ≈ A ⊗ (B ⊗ C).
    This follows from List.flatMap associativity. (docs/collatz.md §3.3) -/
theorem compose_assoc (A B C : Splitter Pos) :
    SplitterEquiv Pos (compose Pos (compose Pos A B) C) (compose Pos A (compose Pos B C)) := by
  intro I n m
  -- Both sides have the same split result due to flatMap associativity
  have h_eq : (compose Pos (compose Pos A B) C).split I = (compose Pos A (compose Pos B C)).split I := by
    -- Unfold compose definitions
    show ((A.split I).flatMap B.split).flatMap C.split = (A.split I).flatMap (fun K => (B.split K).flatMap C.split)
    -- Prove by induction on A.split I
    induction A.split I with
    | nil => simp [List.flatMap]
    | cons head tail ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [ih]
  simp only [h_eq]

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Trivial and Atomic
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A splitter is trivial if Split(I) = {I} (or equivalent: never distinguishes). -/
def isTrivial (S : Splitter Pos) : Prop :=
  ∀ I, ∀ J ∈ S.split I, (∀ n, Sat Pos I n ↔ Sat Pos J n)

/-- A splitter is nontrivial if there exists a case that distinguishes. -/
def isNontrivial (S : Splitter Pos) : Prop := ¬ isTrivial Pos S

/-- A splitter is Atomic if every factorization S ~ A ⊗ B implies A or B is trivial.
    This is the spec-compliant definition from §5. -/
def Atomic (S : Splitter Pos) : Prop :=
  ∀ A B : Splitter Pos, SplitterEquiv Pos S (compose Pos A B) →
    isTrivial Pos A ∨ isTrivial Pos B

/-- A splitter is atomic relative to an admissible class (original definition). -/
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
-- 7.5) Observational Equivalence (Spec §5)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two splitters are observationally equivalent if they induce the same ResEquiv for all depths.
    This is the official equivalence from spec §5. -/
def ObsEq (S T : Splitter Pos) : Prop :=
  ∀ d I0 n m, ResEquiv Pos S d I0 n m ↔ ResEquiv Pos T d I0 n m

/-- ObsEq is reflexive. -/
theorem obsEq_refl (S : Splitter Pos) : ObsEq Pos S S := fun _ _ _ _ => Iff.rfl

/-- ObsEq is symmetric. -/
theorem obsEq_symm (S T : Splitter Pos) : ObsEq Pos S T → ObsEq Pos T S :=
  fun h d I0 n m => (h d I0 n m).symm

/-- ObsEq is transitive. -/
theorem obsEq_trans (S T U : Splitter Pos) : ObsEq Pos S T → ObsEq Pos T U → ObsEq Pos S U :=
  fun hST hTU d I0 n m => (hST d I0 n m).trans (hTU d I0 n m)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7.6) Trivial via ObsEq (Spec §5)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Alternative Trivial definition: S is trivial if ObsEq to Id. -/
def TrivialObs (S : Splitter Pos) : Prop :=
  ∀ I, S.split I = [I]

/-- Atomic per spec §5: if S ~ A ⊗ B then A or B is trivial. -/
def AtomicObs (S : Splitter Pos) : Prop :=
  ∀ A B : Splitter Pos, ObsEq Pos S (compose Pos A B) →
    TrivialObs Pos A ∨ TrivialObs Pos B

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7.7) Observable (Spec §8)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A predicate P is Observable at depth d if it factors through residue classes.
    i.e., if ResEquiv(n,m) then P(n) ↔ P(m). -/
def Observable (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (P : Pos → Prop) : Prop :=
  ∀ n m, ResEquiv Pos S d I0 n m → (P n ↔ P m)

/-- All Case-derived predicates (membership in a case) are observable. -/
theorem case_sat_observable (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (J : Info Pos)
    (hJ : J ∈ Cases Pos S d I0) :
    Observable Pos S d I0 (Sat Pos J) := by
  intro n m hRes
  exact hRes J hJ

/-- Observable predicates are closed under conjunction. -/
theorem observable_and (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (P Q : Pos → Prop)
    (hP : Observable Pos S d I0 P) (hQ : Observable Pos S d I0 Q) :
    Observable Pos S d I0 (fun n => P n ∧ Q n) := by
  intro n m hRes
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨(hP n m hRes).mp hp, (hQ n m hRes).mp hq⟩
  · intro ⟨hp, hq⟩
    exact ⟨(hP n m hRes).mpr hp, (hQ n m hRes).mpr hq⟩

/-- Observable predicates are closed under disjunction. -/
theorem observable_or (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (P Q : Pos → Prop)
    (hP : Observable Pos S d I0 P) (hQ : Observable Pos S d I0 Q) :
    Observable Pos S d I0 (fun n => P n ∨ Q n) := by
  intro n m hRes
  constructor
  · intro h
    cases h with
    | inl hp => left; exact (hP n m hRes).mp hp
    | inr hq => right; exact (hQ n m hRes).mp hq
  · intro h
    cases h with
    | inl hp => left; exact (hP n m hRes).mpr hp
    | inr hq => right; exact (hQ n m hRes).mpr hq

/-- Observable predicates are closed under negation. -/
theorem observable_not (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (P : Pos → Prop)
    (hP : Observable Pos S d I0 P) :
    Observable Pos S d I0 (fun n => ¬ P n) := by
  intro n m hRes
  constructor
  · intro hnp hp
    exact hnp ((hP n m hRes).mpr hp)
  · intro hmp hp
    exact hmp ((hP n m hRes).mp hp)
-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Queue: Persistent Residue Under Dynamics
-- ═══════════════════════════════════════════════════════════════════════════════

variable (Next : Pos → Pos)

/-- Iterate Next t times. -/
def iterate (t : ℕ) (n : Pos) : Pos :=
  match t with
  | 0 => n
  | t + 1 => Next (iterate t n)

/-- Queue(d, n) holds iff residue is invariant along the orbit of n AND n satisfies I0. -/
def Queue (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n : Pos) : Prop :=
  Sat Pos I0 n ∧ ∀ t : ℕ, ResEquiv Pos S d I0 n (iterate Pos Next t n)

/-- Additive property of iterate. -/
theorem iterate_add (t s : ℕ) (n : Pos) :
    iterate Pos Next (t + s) n = iterate Pos Next s (iterate Pos Next t n) := by
  induction s with
  | zero => simp [iterate]
  | succ s ih => simp [iterate, ih]

/-- Cases refinement property: Sat J implies Sat I0. -/
theorem cases_refinement (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (J : Info Pos)
    (hJ : J ∈ Cases Pos S d I0) (n : Pos) (hSatJ : Sat Pos J n) :
    Sat Pos I0 n := by
  induction d generalizing I0 J with
  | zero =>
    simp [Cases] at hJ
    subst hJ
    exact hSatJ
  | succ d ih =>
    simp [Cases, List.mem_flatMap] at hJ
    obtain ⟨K, hK, hSplit⟩ := hJ
    -- K in Cases d I0, J in split K
    -- Sat J -> Sat K (split refinement) -> Sat I0 (IH)
    have hSatK : Sat Pos K n := S.refinement K J hSplit n hSatJ
    exact ih I0 K hK hSatK

/-- Queue is closed under dynamics (orbit stability). -/
theorem queue_orbit_closed (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (n : Pos)
    (hQ : Queue Pos Next S d I0 n) (t : ℕ) :
    Queue Pos Next S d I0 (iterate Pos Next t n) := by
  constructor
  · -- Sat I0 (iterate t n)
    -- n satisfies I0 (from hQ)
    -- n ~ iterate t n (from hQ)
    -- Cases cover n, so exists J covering n. ResEquiv -> J covers iterate. Refinement -> I0.
    obtain ⟨hSatI0, hResAll⟩ := hQ
    -- Find J covering n
    have hCover := cases_cover Pos S d I0 n hSatI0
    obtain ⟨J, hJ, hSatJ_n⟩ := hCover
    -- ResEquiv implies J covers iterate
    have hSatJ_iter : Sat Pos J (iterate Pos Next t n) := (hResAll t J hJ).mp hSatJ_n
    -- Refinement
    exact cases_refinement Pos S d I0 J hJ (iterate Pos Next t n) hSatJ_iter

  · -- ∀ s, ResEquiv ...
    intro s
    obtain ⟨_, hResAll⟩ := hQ
    have h_tn : ResEquiv Pos S d I0 (iterate Pos Next t n) n :=
      resEquiv_symm Pos S d I0 n (iterate Pos Next t n) (hResAll t)
    have h_n_ts : ResEquiv Pos S d I0 n (iterate Pos Next (t + s) n) :=
      hResAll (t + s)
    rw [iterate_add Pos Next t s n] at h_n_ts
    apply resEquiv_trans Pos S d I0 (iterate Pos Next t n) n
    · exact h_tn
    · exact h_n_ts

end RevHalt.Splitter

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks (Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Core types
#print axioms RevHalt.Splitter.Splitter
#print axioms RevHalt.Splitter.Sat
#print axioms RevHalt.Splitter.compose

-- Identity and equivalence
#print axioms RevHalt.Splitter.IdSplitter
#print axioms RevHalt.Splitter.id_compose_left
#print axioms RevHalt.Splitter.id_compose_right
#print axioms RevHalt.Splitter.SplitterEquiv

-- Trivial and Atomic
#print axioms RevHalt.Splitter.isTrivial
#print axioms RevHalt.Splitter.isNontrivial
#print axioms RevHalt.Splitter.Atomic
#print axioms RevHalt.Splitter.isAtomicRelative
#print axioms RevHalt.Splitter.isAtomic
#print axioms RevHalt.Splitter.Prime_RH

-- Cases
#print axioms RevHalt.Splitter.Cases
#print axioms RevHalt.Splitter.cases_card_bound
#print axioms RevHalt.Splitter.cases_cover

-- ResEquiv
#print axioms RevHalt.Splitter.ResEquiv
#print axioms RevHalt.Splitter.resEquiv_refl
#print axioms RevHalt.Splitter.resEquiv_symm
#print axioms RevHalt.Splitter.resEquiv_trans

-- ObsEq
#print axioms RevHalt.Splitter.ObsEq
#print axioms RevHalt.Splitter.obsEq_refl
#print axioms RevHalt.Splitter.obsEq_symm
#print axioms RevHalt.Splitter.obsEq_trans
#print axioms RevHalt.Splitter.TrivialObs
#print axioms RevHalt.Splitter.AtomicObs

-- Observable
#print axioms RevHalt.Splitter.Observable
#print axioms RevHalt.Splitter.case_sat_observable
#print axioms RevHalt.Splitter.observable_and
#print axioms RevHalt.Splitter.observable_or
#print axioms RevHalt.Splitter.observable_not

-- Queue
#print axioms RevHalt.Splitter.iterate
#print axioms RevHalt.Splitter.Queue
#print axioms RevHalt.Splitter.iterate_add
#print axioms RevHalt.Splitter.queue_orbit_closed
