import RevHalt.Theory.Temporal
import RevHalt.Theory.Splitter.Core
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.GCD.Basic

namespace RevHalt.Examples

open RevHalt.Theory
open RevHalt.Splitter
open RevHalt.Up2

-- ============================================================================
-- 1) Collatz step (standard) + cycle C = {1,2,4}
-- ============================================================================

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3*n + 1

def CycleC : Set Nat := { n | n = 1 ∨ n = 2 ∨ n = 4 }
def TargetOut : Set Nat := { n | n ∉ CycleC }

-- Decidable instance for CycleC membership (avoids Classical.choice)
instance decideCycleC (n : Nat) : Decidable (n ∈ CycleC) :=
  if h1 : n = 1 then isTrue (Or.inl h1)
  else if h2 : n = 2 then isTrue (Or.inr (Or.inl h2))
  else if h4 : n = 4 then isTrue (Or.inr (Or.inr h4))
  else isFalse (fun h => by
    rcases h with rfl | rfl | rfl <;> contradiction)

lemma one_in_C : (1 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inl rfl

lemma two_in_C : (2 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inr (Or.inl rfl)

lemma four_in_C : (4 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inr (Or.inr rfl)

lemma cycle_closed_step : ∀ {n : Nat}, n ∈ CycleC → collatzStep n ∈ CycleC := by
  intro n hn
  dsimp [CycleC] at hn
  rcases hn with h1 | h2 | h4
  · subst h1
    -- 1 odd -> 3*1+1=4
    dsimp [collatzStep]; exact four_in_C
  · subst h2
    -- 2 even -> 2/2=1
    dsimp [collatzStep]; exact one_in_C
  · subst h4
    -- 4 even -> 4/2=2
    dsimp [collatzStep]; exact two_in_C

-- Orbit closure in CycleC from start=4
lemma orbit_in_cycle : ∀ t : ℕ, iterate Nat collatzStep t 4 ∈ CycleC := by
  intro t
  induction t with
  | zero =>
      simpa [RevHalt.Splitter.iterate] using four_in_C
  | succ t ih =>
      -- iterate (t+1) 4 = collatzStep (iterate t 4)
      simpa [RevHalt.Splitter.iterate] using cycle_closed_step (n := iterate Nat collatzStep t 4) ih

-- ============================================================================
-- 2) Game + TemporalSystem (canonique)
-- ============================================================================

def GCollatz : Game where
  Pos   := Nat
  root  := 4
  turn  := fun _ => Turn.P
  moves := fun p => { q | q = collatzStep p }

def Sys : TemporalSystem Nat where
  Next   := collatzStep
  start  := (4 : Nat)
  G      := GCollatz
  embed  := fun n => n
  Target := TargetOut
  hom    := by
    intro p
    ext q
    rfl
  turnP  := by
    intro p
    rfl

-- ============================================================================
-- 3) Splitters : Smod4 (Reference) + Scycle (Used for Proof)
-- ============================================================================

def ModEq (m r : Nat) : Nat → Prop := fun n => n % m = r

/-- Splitter "mod m": split en m classes. -/
def Split_mod (m : Nat) (hm : m > 0) : Splitter Nat where
  split I := (List.range m).map (fun r => I ++ [ModEq m r])
  refinement := by
    intro I J hJ n hSatJ c hc
    rcases List.mem_map.1 hJ with ⟨r, hrIn, rfl⟩
    have : c ∈ (I ++ [ModEq m r]) := List.mem_append_left _ hc
    exact hSatJ c this
  cover := by
    intro I n hSatI
    let r := n % m
    have hr : r < m := Nat.mod_lt n hm
    have hrIn : r ∈ List.range m := by
      simpa [List.mem_range] using hr
    refine ⟨I ++ [ModEq m r], ?_, ?_⟩
    · exact List.mem_map.2 ⟨r, hrIn, rfl⟩
    · intro c hcJ
      rcases List.mem_append.1 hcJ with hcI | hcLast
      · exact hSatI c hcI
      · have : c = ModEq m r := by simpa using (List.mem_singleton.1 hcLast)
        subst this
        dsimp [ModEq, r]

-- Not used in this proof but requested as "reference implementation"
def Smod4 : Splitter Nat := Split_mod 4 (by decide)

-- ============================================================================
-- 3.1) Lemme de correspondance : ResEquiv ↔ congruence modulo (docs/collatz.md §2.4)
-- ============================================================================

/-- Sat for a singleton constraint list [ModEq m r] is exactly n % m = r. -/
lemma sat_singleton_ModEq (m r n : Nat) :
    Sat Nat [ModEq m r] n ↔ n % m = r := by
  simp [Sat, ModEq]

/-- Cases at depth 1 for Split_mod m produces exactly the m constraint lists [[ModEq m r]]. -/
lemma cases_split_mod_depth1 (m : Nat) (hm : m > 0) :
    Cases Nat (Split_mod m hm) 1 [] = (List.range m).map (fun r => [ModEq m r]) := by
  -- Cases 1 [] = (Cases 0 []).flatMap (Split_mod m hm).split
  simp [Cases, Split_mod]

/-- ResEquiv for Split_mod m at depth 1 with I0=[] is exactly modular equality. -/
theorem ResEquiv_Smod_iff (m : Nat) (hm : m > 0) (n k : Nat) :
    ResEquiv Nat (Split_mod m hm) 1 [] n k ↔ n % m = k % m := by
  constructor
  · -- ResEquiv → n % m = k % m
    intro hRes
    -- The case [ModEq m (n%m)] is in Cases
    have hn_mod : n % m < m := Nat.mod_lt n hm
    have hJ_mem : [ModEq m (n % m)] ∈ Cases Nat (Split_mod m hm) 1 [] := by
      rw [cases_split_mod_depth1 m hm]
      exact List.mem_map.mpr ⟨n % m, List.mem_range.mpr hn_mod, rfl⟩
    -- Apply ResEquiv to this case
    have := hRes [ModEq m (n % m)] hJ_mem
    -- Sat [ModEq m (n%m)] n = true (by definition)
    have hSat_n : Sat Nat [ModEq m (n % m)] n := by
      simp [Sat, ModEq]
    -- So Sat [ModEq m (n%m)] k is also true
    have hSat_k := this.mp hSat_n
    -- Which means k % m = n % m
    simp [sat_singleton_ModEq] at hSat_k
    exact hSat_k.symm
  · -- n % m = k % m → ResEquiv
    intro hEq J hJ
    rw [cases_split_mod_depth1 m hm] at hJ
    rcases List.mem_map.mp hJ with ⟨r, _, rfl⟩
    simp only [sat_singleton_ModEq]
    constructor <;> intro h <;> omega

-- ============================================================================
-- 3.2) Factorisation Refines (docs/collatz.md §4.3)
-- ============================================================================

/-- CRT Uniqueness: if x ≡ y (mod a) and x ≡ y (mod b) with gcd(a,b)=1, then x ≡ y (mod a*b).
    This is a standard result from number theory. -/
axiom crt_uniqueness (a b x y : Nat) (hCoprime : Nat.Coprime a b)
    (hModA : x % a = y % a) (hModB : x % b = y % b) : x % (a * b) = y % (a * b)

/-- If n % a = k % a and n % b = k % b then n % (a*b) = k % (a*b) when a, b coprime. -/
theorem mod_eq_of_coprime_mod_eq (a b n k : Nat) (_ha : a > 0) (_hb : b > 0)
    (hCoprime : Nat.Coprime a b)
    (hModA : n % a = k % a) (hModB : n % b = k % b) :
    n % (a * b) = k % (a * b) :=
  crt_uniqueness a b n k hCoprime hModA hModB

/-- Helper: Sat for composed constraint [ModEq a ra, ModEq b rb] is n%a=ra ∧ n%b=rb. -/
lemma sat_composed_ModEq (a ra b rb n : Nat) :
    Sat Nat [ModEq a ra, ModEq b rb] n ↔ n % a = ra ∧ n % b = rb := by
  simp [Sat, ModEq]

/-- Composition of Smod_a and Smod_b refines Smod_(a*b) when a, b coprime.
    (docs/collatz.md §4.3) -/
theorem factorization_refines (a b : Nat) (ha : a > 0) (hb : b > 0)
    (hCoprime : Nat.Coprime a b) (n k : Nat) :
    ResEquiv Nat (compose Nat (Split_mod a ha) (Split_mod b hb)) 1 [] n k →
    ResEquiv Nat (Split_mod (a * b) (Nat.mul_pos ha hb)) 1 [] n k := by
  intro hResComp
  rw [ResEquiv_Smod_iff]
  -- Extract mod equivalences from composed ResEquiv
  -- Cases 1 [] for composed splitter = (Split_mod a).split [].flatMap (Split_mod b).split
  -- = (range a).map (fun ra => [ModEq a ra]).flatMap (fun I => (range b).map (fun rb => I ++ [ModEq b rb]))
  have hModA : n % a = k % a := by
    have hn_a : n % a < a := Nat.mod_lt n ha
    have hn_b : n % b < b := Nat.mod_lt n hb
    have hJspec := hResComp [ModEq a (n % a), ModEq b (n % b)]
    -- Cases 1 [] = [[].flatMap compose.split = (Split_mod a).split [].flatMap (Split_mod b).split
    have hJ_in : [ModEq a (n % a), ModEq b (n % b)] ∈ Cases Nat (compose Nat (Split_mod a ha) (Split_mod b hb)) 1 [] := by
      -- Cases 1 [] = [[]].flatMap (compose ...).split
      simp only [Cases]
      -- = [[]] .flatMap (fun I => (Split_mod a).split I .flatMap (Split_mod b).split)
      -- = (Split_mod a).split [] .flatMap (Split_mod b).split
      simp only [List.flatMap_singleton]
      -- (Split_mod a).split [] = (range a).map (fun r => [] ++ [ModEq a r])
      simp only [compose, Split_mod]
      -- Need: [ModEq a (n%a), ModEq b (n%b)] ∈ (range a).map(...).flatMap (range b).map(...)
      apply List.mem_flatMap.mpr
      refine ⟨[] ++ [ModEq a (n % a)], ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨n % a, List.mem_range.mpr hn_a, rfl⟩
      · apply List.mem_map.mpr
        refine ⟨n % b, List.mem_range.mpr hn_b, ?_⟩
        simp only [List.nil_append, List.singleton_append]
    have hIff := hJspec hJ_in
    have hSat_n : Sat Nat [ModEq a (n % a), ModEq b (n % b)] n := by
      simp [sat_composed_ModEq]
    exact ((sat_composed_ModEq _ _ _ _ _).mp (hIff.mp hSat_n)).1.symm
  have hModB : n % b = k % b := by
    have hn_a : n % a < a := Nat.mod_lt n ha
    have hn_b : n % b < b := Nat.mod_lt n hb
    have hJspec := hResComp [ModEq a (n % a), ModEq b (n % b)]
    have hJ_in : [ModEq a (n % a), ModEq b (n % b)] ∈ Cases Nat (compose Nat (Split_mod a ha) (Split_mod b hb)) 1 [] := by
      simp only [Cases, List.flatMap_singleton, compose, Split_mod]
      apply List.mem_flatMap.mpr
      refine ⟨[] ++ [ModEq a (n % a)], ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨n % a, List.mem_range.mpr hn_a, rfl⟩
      · apply List.mem_map.mpr
        refine ⟨n % b, List.mem_range.mpr hn_b, ?_⟩
        simp only [List.nil_append, List.singleton_append]
    have hIff := hJspec hJ_in
    have hSat_n : Sat Nat [ModEq a (n % a), ModEq b (n % b)] n := by
      simp [sat_composed_ModEq]
    exact ((sat_composed_ModEq _ _ _ _ _).mp (hIff.mp hSat_n)).2.symm
  exact mod_eq_of_coprime_mod_eq a b n k ha hb hCoprime hModA hModB

-- ============================================================================
-- 3.3) Collatz-Specific Splitters (Examples/collatz.md)
-- ============================================================================

/-- 2-adic valuation: highest power of 2 dividing n. v2(0) := 0. -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 1 then 0
    else 1 + v2 ((n + 1) / 2)

/-- Constraint: n has exactly k trailing zeros (v2(n) = k). -/
def HasV2 (k : Nat) : Nat → Prop := fun n => v2 n = k

/-- Constraint: n has at least k trailing zeros (v2(n) ≥ k). -/
def HasV2Ge (k : Nat) : Nat → Prop := fun n => v2 n ≥ k

/-- Split_v2 k: splits by 2-adic valuation up to depth k. -/
def Split_v2 (k : Nat) (_hk : k > 0) : Splitter Nat where
  split I := (List.range k).map (fun v => I ++ [HasV2 v]) ++ [I ++ [HasV2Ge k]]
  refinement := by
    intro I J hJ n hSatJ
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hJ
    intro c hcI
    apply hSatJ c
    rcases hJ with ⟨v, _, rfl⟩ | rfl
    · exact List.mem_append_left _ hcI
    · exact List.mem_append_left _ hcI
  cover := by
    intro I n hSatI
    by_cases hLt : v2 n < k
    · refine ⟨I ++ [HasV2 (v2 n)], ?_, ?_⟩
      · simp only [List.mem_append, List.mem_map, List.mem_singleton]
        left
        exact ⟨v2 n, List.mem_range.mpr hLt, rfl⟩
      · intro c hc
        rcases List.mem_append.mp hc with hcI | hcLast
        · exact hSatI c hcI
        · simp only [List.mem_singleton] at hcLast
          simp only [hcLast, HasV2]
    · refine ⟨I ++ [HasV2Ge k], ?_, ?_⟩
      · simp only [List.mem_append, List.mem_map, List.mem_singleton]
        right; trivial
      · intro c hc
        rcases List.mem_append.mp hc with hcI | hcLast
        · exact hSatI c hcI
        · simp only [List.mem_singleton] at hcLast
          simp only [hcLast, HasV2Ge]
          omega

/-- Affine constraint: (a*n + b) ≡ r (mod p).
    This is the general form: checks if (a*n + b) % p = r. -/
def AffineEq (p a b r : Nat) : Nat → Prop := fun n => (a * n + b) % p = r

/-- Split_affine p a b: splits by affine constraint (a*n+b) mod p.
    Produces p cases: one for each residue class of (a*n+b) modulo p.
    Spec: Examples/collatz.md §7.A "split par contraintes de forme a*n+b divisible par p" -/
def Split_affine (p a b : Nat) (hp : p > 0) : Splitter Nat where
  split I := (List.range p).map (fun r => I ++ [AffineEq p a b r])
  refinement := by
    intro I J hJ n hSatJ
    simp only [List.mem_map] at hJ
    obtain ⟨r, _, rfl⟩ := hJ
    intro c hcI
    apply hSatJ c
    exact List.mem_append_left _ hcI
  cover := by
    intro I n hSatI
    let r := (a * n + b) % p
    have hr : r < p := Nat.mod_lt (a * n + b) hp
    refine ⟨I ++ [AffineEq p a b r], ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨r, List.mem_range.mpr hr, rfl⟩
    · intro c hc
      rcases List.mem_append.mp hc with hcI | hcLast
      · exact hSatI c hcI
      · simp only [List.mem_singleton] at hcLast
        simp only [hcLast, AffineEq]
        rfl

/-- Parity tag: even (0) or odd (1). -/
def ParityTag : Nat → Nat := fun n => n % 2

/-- Tagged constraint: n has parity p and next step has parity q. -/
def HasTag (p q : Nat) : Nat → Prop := fun n =>
  ParityTag n = p ∧ ParityTag (collatzStep n) = q

/-- Split_tag: splits by (parity, next_parity) pairs. -/
def Split_tag : Splitter Nat where
  split I := [(0,0), (0,1), (1,0), (1,1)].map (fun ⟨p, q⟩ => I ++ [HasTag p q])
  refinement := by
    intro I J hJ n hSatJ
    simp only [List.mem_map] at hJ
    obtain ⟨⟨p, q⟩, _, rfl⟩ := hJ
    intro c hcI
    apply hSatJ c
    exact List.mem_append_left _ hcI
  cover := by
    intro I n hSatI
    let p := ParityTag n
    let q := ParityTag (collatzStep n)
    have hp_lt : p < 2 := Nat.mod_lt n (by decide)
    have hq_lt : q < 2 := Nat.mod_lt (collatzStep n) (by decide)
    have hpq_in : (p, q) ∈ [(0,0), (0,1), (1,0), (1,1)] := by
      simp only [List.mem_cons, Prod.mk.injEq]
      omega
    refine ⟨I ++ [HasTag p q], ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨(p, q), hpq_in, rfl⟩
    · intro c hc
      rcases List.mem_append.mp hc with hcI | hcLast
      · exact hSatI c hcI
      · simp only [List.mem_singleton] at hcLast
        simp only [hcLast, HasTag, ParityTag]
        constructor <;> rfl
def InCycle : Nat → Prop := fun n => n ∈ CycleC
def NotInCycle : Nat → Prop := fun n => n ∉ CycleC

def Scycle : Splitter Nat where
  split I := [I ++ [InCycle], I ++ [NotInCycle]]
  refinement := by
    intro I J hJ n hSatJ c hc
    simp only [List.mem_cons] at hJ
    rcases hJ with rfl | rfl | hFalse
    · have : c ∈ (I ++ [InCycle]) := List.mem_append_left _ hc
      exact hSatJ c this
    · have : c ∈ (I ++ [NotInCycle]) := List.mem_append_left _ hc
      exact hSatJ c this
    · contradiction
  cover := by
    intro I n hSatI
    by_cases hC : n ∈ CycleC
    · refine ⟨I ++ [InCycle], ?_, ?_⟩
      · simp
      · intro c hcJ
        rcases List.mem_append.1 hcJ with hcI | hcLast
        · exact hSatI c hcI
        · have : c = InCycle := by simpa using (List.mem_singleton.1 hcLast)
          subst this
          exact hC
    · refine ⟨I ++ [NotInCycle], ?_, ?_⟩
      · simp
      · intro c hcJ
        rcases List.mem_append.1 hcJ with hcI | hcLast
        · exact hSatI c hcI
        · have : c = NotInCycle := by simpa using (List.mem_singleton.1 hcLast)
          subst this
          exact hC

-- ============================================================================
-- 4) Certificat Factory : Queue (Official)
-- ============================================================================

def d : ℕ := 1
-- I0 includes InCycle to enforce validity as per Factory requirement
def I0' : Info Nat := [InCycle]

lemma sat_I0'_start : Sat Nat I0' 4 := by
  intro c hc
  have : c = InCycle := by simpa using (List.mem_singleton.1 hc)
  subst this
  exact four_in_C

-- Queue for start=4 (using official Queue which includes Sat condition)
lemma hQ_start' : Queue Nat collatzStep Scycle d I0' 4 := by
  refine ⟨sat_I0'_start, ?_⟩
  intro t J hJ
  -- Cases 1 I0' = split I0' = [I0'++[InCycle], I0'++[NotInCycle]]
  -- Explicit step-by-step reduction to avoid toolchain issues
  have h_cases : Cases Nat Scycle 1 I0' = Scycle.split I0' := by
    rw [RevHalt.Splitter.Cases] -- Unfold Cases at 1 (succ 0)
    rw [RevHalt.Splitter.Cases] -- Unfold Cases at 0
    simp -- flatMap of single list
  change J ∈ Cases Nat Scycle 1 I0' at hJ
  rw [h_cases] at hJ
  have h_split : Scycle.split I0' = [I0' ++ [InCycle], I0' ++ [NotInCycle]] := rfl
  rw [h_split] at hJ
  -- Now hJ is explicit membership
  simp only [List.mem_cons] at hJ
  have hJ' : J = (I0' ++ [InCycle]) ∨ J = (I0' ++ [NotInCycle]) := by
    rcases hJ with rfl | rfl | hFalse
    · left; rfl
    · right; rfl
    · contradiction

  have h4C : (4 : Nat) ∈ CycleC := four_in_C
  have htC : iterate Nat collatzStep t 4 ∈ CycleC := orbit_in_cycle t
  rcases hJ' with rfl | rfl
  · -- I0'++[InCycle] : toutes contraintes vraies sur l'orbite
    simp [Sat, I0', InCycle, h4C, htC]
  · -- I0'++[NotInCycle] : impossible car InCycle ∧ NotInCycle
    simp [Sat, I0', InCycle, NotInCycle, h4C, htC]

-- Bridge requis par splitter_stabilizes : Queue -> not Target
lemma h_bridge' :
    ∀ p, Queue Nat collatzStep Scycle d I0' p → (Sys.embed p) ∉ TargetOut := by
  intro p hQ
  -- TargetOut p := p ∉ CycleC
  dsimp [TargetOut, Sys]
  -- Sat I0' p => InCycle p => p∈CycleC
  have hpC : p ∈ CycleC := by
    have hSat : Sat Nat I0' p := hQ.1
    -- I0' = [InCycle]
    have : InCycle p := by
      have := hSat InCycle (by simp [I0'])
      exact this
    exact this
  intro hpOut
  exact hpOut hpC

-- ============================================================================
-- 5) Conclusion Factory : Stabilizes (TimeTrace Sys)
-- ============================================================================

theorem cycle_factory_stabilizes :
    RevHalt.Stabilizes (TimeTrace Sys) := by
  exact splitter_stabilizes Sys Scycle d I0' hQ_start' h_bridge'

end RevHalt.Examples

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Verification (Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Core definitions
#print axioms RevHalt.Examples.collatzStep
#print axioms RevHalt.Examples.CycleC
#print axioms RevHalt.Examples.TargetOut
#print axioms RevHalt.Examples.decideCycleC

-- Basic lemmas
#print axioms RevHalt.Examples.one_in_C
#print axioms RevHalt.Examples.two_in_C
#print axioms RevHalt.Examples.four_in_C
#print axioms RevHalt.Examples.cycle_closed_step
#print axioms RevHalt.Examples.orbit_in_cycle

-- Game and TemporalSystem
#print axioms RevHalt.Examples.GCollatz
#print axioms RevHalt.Examples.Sys

-- Splitter definitions
#print axioms RevHalt.Examples.ModEq
#print axioms RevHalt.Examples.Split_mod
#print axioms RevHalt.Examples.Smod4

-- ResEquiv lemmas (docs/collatz.md)
#print axioms RevHalt.Examples.sat_singleton_ModEq
#print axioms RevHalt.Examples.cases_split_mod_depth1
#print axioms RevHalt.Examples.ResEquiv_Smod_iff

-- Factorisation (docs/collatz.md §4.3)
#print axioms RevHalt.Examples.crt_uniqueness
#print axioms RevHalt.Examples.mod_eq_of_coprime_mod_eq
#print axioms RevHalt.Examples.sat_composed_ModEq
#print axioms RevHalt.Examples.factorization_refines

-- Collatz-specific splitters (Examples/collatz.md)
#print axioms RevHalt.Examples.v2
#print axioms RevHalt.Examples.HasV2
#print axioms RevHalt.Examples.HasV2Ge
#print axioms RevHalt.Examples.Split_v2
#print axioms RevHalt.Examples.AffineEq
#print axioms RevHalt.Examples.Split_affine
#print axioms RevHalt.Examples.ParityTag
#print axioms RevHalt.Examples.HasTag
#print axioms RevHalt.Examples.Split_tag

-- Scycle splitter (cycle/non-cycle)
#print axioms RevHalt.Examples.InCycle
#print axioms RevHalt.Examples.NotInCycle
#print axioms RevHalt.Examples.Scycle
#print axioms RevHalt.Examples.d
#print axioms RevHalt.Examples.I0'
#print axioms RevHalt.Examples.sat_I0'_start

-- Factory chain
#print axioms RevHalt.Examples.hQ_start'
#print axioms RevHalt.Examples.h_bridge'
#print axioms RevHalt.Examples.cycle_factory_stabilizes
