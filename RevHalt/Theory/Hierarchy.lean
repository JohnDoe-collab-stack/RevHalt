import RevHalt.Theory.Stabilization
import RevHalt.Theory.Up2
import RevHalt.Theory.Splitter.AvoidanceBridge
import RevHalt.Theory.Splitter.Core

/-!
# RevHalt.Theory.Hierarchy

This module serves as the **unification layer** for the RevHalt theory components:

1.  **Up1 (Stabilization)**: Temporal safety ($\Pi_1$). "Never Halts".
2.  **Up2 (Avoidance)**: Structural safety ($\Pi_2$). "Winning Strategy to avoid Halting".
3.  **Splitter (Resolution)**: Arithmetic safety. "Resolvable into stable Prime components".

## The Hierarchy Theorem

We demonstrate the implications:
`Splitter (Resolution) → Up2 (Avoidance) → Up1 (Stabilization)`

This formalizes the intuition that arithmetical structure implies structural game stability,
which implies temporal non-halting.
-/

namespace RevHalt.Hierarchy

open RevHalt.Splitter
open RevHalt.Up2
open RevHalt.Bridge

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. Setup: The "Run Game"
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A generic embedding of a Trace into a Game structure.
The trace `T` corresponds to hitting a `Target` in the game `G`.
-/
structure TraceGameEmbedding (Pos : Type) where
  T : Pos → Prop -- Generalized Trace
  G : Game
  embed : Pos → G.Pos
  Target : Set G.Pos
  /-- If the embedding hits the target, the trace halts at that index. -/
  target_spec : ∀ n, embed n ∈ Target ↔ T n

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. Up2 → Up1 (Pointwise Safety)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Lemma: Immediate Safety.**
If `p` is in the Avoid2Set (infinite safety kernel), it is not in the Target.
-/
theorem avoid2_implies_not_target
    (G : Game) (Target : Set G.Pos) (p : G.Pos)
    (h : Avoid2Mem G Target p) : p ∉ Target := by
  -- Unfold definitions (Avoid2Mem is alias for p ∈ Avoid2Set)
  rw [Avoid2Mem, Avoid2Set] at h
  rcases h with ⟨X, hClosed, hpX⟩
  -- AvoidClosed implies X ⊆ AvoidStep(Target, X)
  have hStep := hClosed hpX
  -- AvoidStep contains `p ∉ Target`
  exact hStep.1

/--
**Theorem: Avoidance implies Stabilization (Pointwise).**
If the starting position `n` is in the `Avoid2Set` of the game,
then the trace `T` is false at `n`.
-/
theorem up2_implies_up1_pointwise
    {Pos : Type} (emb : TraceGameEmbedding Pos)
    (n : Pos)
    (hAvoid : Avoid2Mem emb.G emb.Target (emb.embed n))
    : ¬ emb.T n := by
  -- hAvoid implies embed n ∉ Target
  have hNotTarget := avoid2_implies_not_target emb.G emb.Target (emb.embed n) hAvoid
  -- Trace spec: embed n ∈ Target ↔ T n
  rw [← emb.target_spec n]
  exact hNotTarget

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. Splitter → Up2 (Resolution implies Avoidance)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Theorem: Splitter Resolution implies Avoidance.**
If a position `n` is covered by a valid Splitter/Queue whose cases are safe,
then `n` is in the Avoid2Set (Infinite Safety Kernel).
-/
theorem splitter_implies_avoid2
    (Pos : Type) (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (Next : Pos → Pos)
    (G : Game) (embed : Pos → G.Pos) (Target : Set G.Pos)
    (h_hom : ∀ n, G.moves (embed n) = {embed (Next n)})
    (h_turn : ∀ n, G.turn (embed n) = Turn.P)
    (h_safe : ∀ n, Queue Pos Next S d I0 n → embed n ∉ Target)
    (n : Pos) (hQ : Queue Pos Next S d I0 n)
    : Avoid2Mem G Target (embed n) := by
  -- We use the Bridge theorem
  dsimp [Avoid2Mem]
  exact queue_splitter_subset_avoid2 Pos S d I0 Next G embed Target h_hom h_turn h_safe n hQ

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4. The Hierarchy Chain (Pointwise)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**The Grand Unification (Pointwise).**
Splitter Safety guarantees Pointwise Safety via Up2.
-/
theorem hierarchy_chain
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (Next : Pos → Pos)
    (emb : TraceGameEmbedding Pos)
    -- Hypotheses linking the components
    (h_hom : ∀ n, emb.G.moves (emb.embed n) = {emb.embed (Next n)})
    (h_turn : ∀ n, emb.G.turn (emb.embed n) = Turn.P)
    (h_safe : ∀ n, Queue Pos Next S d I0 n → emb.embed n ∉ emb.Target)
    -- The instance
    (n : Pos) (hQ : Queue Pos Next S d I0 n)
    : ¬ emb.T n := by
  -- 1. Splitter -> Up2 (Avoidance)
  have hAvoid := splitter_implies_avoid2 Pos S d I0 Next emb.G emb.embed emb.Target h_hom h_turn h_safe n hQ

  -- 2. Up2 -> Up1 (Pointwise Stabilization)
  exact up2_implies_up1_pointwise emb n hAvoid

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5. Temporal Stabilization (Full Up1)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Temporal Embedding**:
Specializes the embedding to a time-evolution context.
We assume the existence of a `Next` function on `Pos` representing time steps.
The trace `T` is now understood as `T k` meaning "Halts at step k" (or state `Next^k n0`).
-/
structure TemporalEmbedding (Pos : Type) extends TraceGameEmbedding Pos where
  Next : Pos → Pos
  /-- The Game moves match the State transitions. -/
  homomorphism : ∀ p, G.moves (embed p) = {embed (Next p)}
  /-- The trace property is stable if it holds for the trajectory starting at `start`. -/
  start : Pos

/--
**Theorem: Splitter implies Full Stabilization.**
If the starting position is covered by a valid Queue splitter,
then the system *never* halts (Stabilizes).

Proof:
1. `Queue` is closed under `Next` (orbit stability).
2. Thus, for all `k`, `Queue` holds at `Next^k start`.
3. By `splitter_implies_avoid2`, every point in the trajectory is in `Avoid2Set`.
4. By `avoid2_implies_not_target`, no point in the trajectory is in `Target`.
5. By `target_spec`, `T` is false for every point in the trajectory.
-/
theorem stabilization_chain
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos) (Next : Pos → Pos)
    (emb : TemporalEmbedding Pos)
    -- Hypotheses
    (h_emb_hom : ∀ p, emb.G.moves (emb.embed p) = {emb.embed (Next p)})
    (h_emb_turn : ∀ p, emb.G.turn (emb.embed p) = Turn.P)
    (h_safe : ∀ p, Queue Pos Next S d I0 p → emb.embed p ∉ emb.Target)
    -- Start condition
    (hQ : Queue Pos Next S d I0 emb.start)
    -- Matching the generic Next with embedding Next explicitely if needed (they are the same here)
    : ∀ k, ¬ emb.T (iterate Pos Next k emb.start) := by
  intro k
  -- 1. Orbit Closure of Queue
  -- NOTE: iterate takes (Pos Next k start) in that order in Core.lean
  have hQ_k : Queue Pos Next S d I0 (iterate Pos Next k emb.start) :=
    queue_orbit_closed Pos Next S d I0 emb.start hQ k

  -- 2. Apply Hierarchy Chain to the k-th point
  let current_pos := iterate Pos Next k emb.start

  -- We reuse hierarchy_chain pointwise
  apply hierarchy_chain Pos S d I0 Next emb.toTraceGameEmbedding h_emb_hom h_emb_turn h_safe current_pos hQ_k

end RevHalt.Hierarchy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6. Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

namespace RevHalt.Hierarchy
#print axioms avoid2_implies_not_target
#print axioms up2_implies_up1_pointwise
#print axioms splitter_implies_avoid2
#print axioms hierarchy_chain
#print axioms stabilization_chain
end RevHalt.Hierarchy
