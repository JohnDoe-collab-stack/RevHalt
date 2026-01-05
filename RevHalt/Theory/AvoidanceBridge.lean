import RevHalt.Theory.Splitter
import RevHalt.Theory.Up2
import Mathlib.Data.Set.Basic

namespace RevHalt.Bridge

open RevHalt.Splitter
open RevHalt.Up2

/--
The Bridge Theorem:
If a deterministic system (Queue) is embedded into a game,
then Queue-stable positions lie in the Avoid2Set (infinite safety kernel).

This connects the arithmetic/splitter notion of stability to the structural game notion of avoidance.
-/
theorem queue_splitter_subset_avoid2
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (Next : Pos → Pos)
    (G : Game)
    (embed : Pos → G.Pos)
    (Target : Set G.Pos)
    -- Hypotheses:
    (h_hom : ∀ n, G.moves (embed n) = {embed (Next n)}) -- Strict deterministic embedding
    (h_turn : ∀ n, G.turn (embed n) = Turn.P) -- Modeled as P-turn (or O-turn with hasMove)
    (h_safe : ∀ n, Queue Pos Next S d I0 n → embed n ∉ Target) -- Queue implies local safety
    :
    ∀ n, Queue Pos Next S d I0 n → embed n ∈ Avoid2Set G Target := by
  intro n0 hQ0

  -- Define the candidate set X as the set of embedded Queue positions
  let X : Set G.Pos := { p | ∃ m, p = embed m ∧ Queue Pos Next S d I0 m }

  have hX : embed n0 ∈ X := ⟨n0, rfl, hQ0⟩

  -- Show X is AvoidClosed
  have hClosed : AvoidClosed G Target X := by
    intro p hp
    rcases hp with ⟨m, rfl, hQm⟩

    -- 1. p not in Target
    have hNotTarget : embed m ∉ Target := h_safe m hQm

    -- 2. P-moves stay in X
    have hP : G.turn (embed m) = Turn.P → ∀ q, q ∈ G.moves (embed m) → q ∈ X := by
      intro _ q hqMove
      rw [h_hom m] at hqMove
      change q = embed (Next m) at hqMove
      have hEq : q = embed (Next m) := hqMove
      rw [hEq]
      -- Use orbit closure of Queue
      have hQNext : Queue Pos Next S d I0 (Next m) :=
        queue_orbit_closed Pos Next S d I0 m hQm 1
      exact ⟨Next m, rfl, hQNext⟩

    -- 3. O-moves (vacuous if turn is P)
    have hO : G.turn (embed m) = Turn.O → G.hasMove (embed m) → ∃ q, q ∈ G.moves (embed m) ∧ q ∈ X := by
      intro hTurnO _
      -- Contradiction with h_turn
      have hTurnP := h_turn m
      rw [hTurnP] at hTurnO
      contradiction

    -- Combine into AvoidStep
    refine ⟨hNotTarget, hP, hO⟩

  -- Apply Avoid2Set_largest (X is a post-fixed point, so X ⊆ Avoid2Set)
  have hSubset : X ⊆ Avoid2Set G Target := Avoid2Set_largest G Target X hClosed

  exact hSubset hX

end RevHalt.Bridge
