import RevHalt.Theory.Temporal
import RevHalt.Theory.Splitter.Core
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic


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
-- 3) Splitter Oracle / Sémantique : Scycle
--    Ce splitter sert à tester l'intégration du pipeline (Factory).
--    Il utilise directement la propriété sémantique "InCycle" (∈ {1,2,4}).
--    CE N'EST PAS un certificat arithmétique (pas mod/v2/affine).
-- ============================================================================

def InCycle : Nat → Prop := fun n => n ∈ CycleC
def NotInCycle : Nat → Prop := fun n => n ∉ CycleC

/-- Scycle is an ORACLE / SEMANTIC splitter for testing the factory pipeline.
    It splits based on the semantic property "n ∈ CycleC" directly.
    It is NOT an arithmetic splitter in the refined sense (not built from mod/v2/affine).
    It serves to validate the Queue -> Avoid2 -> Stabilizes chain. -/
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
