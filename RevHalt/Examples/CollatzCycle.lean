import RevHalt.Theory.Up2
import RevHalt.Theory.Temporal
import Mathlib.Data.Set.Basic

namespace RevHalt.Examples

open RevHalt.Up2
open RevHalt.Theory
open RevHalt.Splitter -- Added for iterate access if needed

-- ============================================================================
-- 1) Collatz step (standard)
-- ============================================================================

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3*n + 1

-- ============================================================================
-- 2) The trivial cycle set C = {1,2,4}
--    We will prove: starting from 4, the orbit never leaves C.
--    So: Target := complement(C).
-- ============================================================================

def CycleC : Set Nat := { n | n = 1 ∨ n = 2 ∨ n = 4 }

def TargetOut : Set Nat := { n | n ∉ CycleC }

lemma one_in_C : (1 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inl rfl

lemma two_in_C : (2 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inr (Or.inl rfl)

lemma four_in_C : (4 : Nat) ∈ CycleC := by
  dsimp [CycleC]; exact Or.inr (Or.inr rfl)

-- Closure of the cycle under collatzStep:
-- collatzStep 1 = 4, collatzStep 2 = 1, collatzStep 4 = 2
lemma cycle_closed_step : ∀ {n : Nat}, n ∈ CycleC → collatzStep n ∈ CycleC := by
  intro n hn
  dsimp [CycleC] at hn
  rcases hn with h1 | h2 | h4
  · -- n = 1
    subst h1
    -- 1 is odd, so 3*1+1 = 4
    dsimp [collatzStep]
    exact four_in_C
  · -- n = 2
    subst h2
    -- 2 is even, so 2/2 = 1
    dsimp [collatzStep]
    exact one_in_C
  · -- n = 4
    subst h4
    -- 4 is even, so 4/2 = 2
    dsimp [collatzStep]
    exact two_in_C

-- ============================================================================
-- 3) Build the deterministic Game instance G for the dynamical system
--    - Pos := Nat
--    - turn := P everywhere
--    - moves p := { collatzStep p }
-- ============================================================================

def GCollatz : Game where
  Pos   := Nat
  root  := 4
  turn  := fun _ => Turn.P
  moves := fun p => { q | q = collatzStep p }

-- Convenience: membership in moves is equality to collatzStep
lemma mem_moves_iff (p q : Nat) :
    q ∈ (GCollatz.moves p) ↔ q = collatzStep p := by
  rfl

-- ============================================================================
-- 4) Prove Avoid2Mem for all points in CycleC wrt TargetOut
--    We exhibit X := CycleC as a post-fixed point of AvoidStep(TargetOut, X).
-- ============================================================================

def X : Set Nat := CycleC

-- Post-fixedness: X ⊆ AvoidStep(TargetOut, X)
lemma X_postfixed :
    AvoidClosed GCollatz TargetOut X := by
  intro p hpX
  -- Need: p ∈ AvoidStep G TargetOut X
  -- AvoidStep requires:
  --   p ∉ TargetOut  (i.e., p ∈ CycleC)
  --   P-turn implies all moves stay in X
  --   O-part irrelevant (vacuous: turn != O)
  refine ?_
  dsimp [AvoidStep, TargetOut, X]
  refine And.intro ?h_notTarget (And.intro ?hP ?hO)

  · -- p ∉ TargetOut
    -- TargetOut p := p ∉ CycleC, so not(TargetOut p) means p ∈ CycleC
    -- hpX : p ∈ CycleC
    intro hpOut
    exact hpOut hpX

  · -- P case: if turn=P, all moves stay in X
    intro hTurn q hqMove
    -- moves are singleton: q = collatzStep p
    have hq : q = collatzStep p := (mem_moves_iff p q).1 hqMove
    subst hq
    -- show collatzStep p ∈ CycleC using closure lemma
    exact cycle_closed_step (n := p) hpX

  · -- O case: if turn=O, hasMove -> ∃ move staying in X
    -- Here turn is always P, so this is trivially satisfied.
    intro hTurn
    -- contradiction since turn p = P
    have : GCollatz.turn p = Turn.P := rfl
    rw [this] at hTurn
    contradiction

-- Therefore any p ∈ X is in Avoid2Set(TargetOut)
lemma cycle_points_in_Avoid2 :
    ∀ {p : Nat}, p ∈ CycleC → Avoid2Mem GCollatz TargetOut p := by
  intro p hpC
  -- Avoid2Mem means p ∈ Avoid2Set = ∃X, AvoidClosed X ∧ p∈X
  dsimp [Avoid2Mem, Avoid2Set]
  exact ⟨X, X_postfixed, hpC⟩

-- In particular, start=4 is in Avoid2Mem
lemma start_in_Avoid2 : Avoid2Mem GCollatz TargetOut (4 : Nat) := by
  exact cycle_points_in_Avoid2 (p := 4) four_in_C

-- ============================================================================
-- 5) Instantiate the canonical TemporalSystem and conclude Stabilizes
-- ============================================================================

def SysCycle : TemporalSystem Nat where
  Next   := collatzStep
  start  := (4 : Nat)
  G      := GCollatz
  embed  := fun n => n
  Target := TargetOut
  hom    := by
    intro p
    -- moves (embed p) = { embed (Next p) }
    -- moves p := {q | q = collatzStep p}
    ext q
    constructor <;> intro h
    · exact h
    · exact h
  turnP  := by
    intro p
    rfl

-- Local iterate to bypass type inference issues with Splitter.iterate
def iterate_nat (f : Nat → Nat) (k : Nat) (n : Nat) : Nat :=
  match k with
  | 0 => n
  | k+1 => f (iterate_nat f k n)

@[simp] lemma iterate_nat_zero (f : Nat → Nat) (n : Nat) :
  iterate_nat f 0 n = n := rfl

@[simp] lemma iterate_nat_succ (f : Nat → Nat) (k : Nat) (n : Nat) :
  iterate_nat f (k+1) n = f (iterate_nat f k n) := rfl

theorem cycle_never_leaves :
    RevHalt.Stabilizes (fun k => (iterate_nat collatzStep k 4) ∈ TargetOut) := by
  -- Use the generic temporal theorem: membership in Avoid2Set yields not Target at each time.
  intro k
  -- show orbit point is in CycleC, hence not in TargetOut, hence TimeTrace false.
  -- orbit_pt using iterate_nat
  let pt := iterate_nat collatzStep k (4 : Nat)
  have hptC : pt ∈ CycleC := by
    -- Induction
    induction k with
    | zero =>
        simp [pt, iterate_nat_zero, four_in_C]
    | succ k ih =>
        simpa [pt, iterate_nat_succ] using cycle_closed_step ih
  -- TimeTrace logic
  dsimp [TargetOut]
  intro hOut
  exact hOut hptC

end RevHalt.Examples
