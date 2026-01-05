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
Now includes structural constraints `hom` and `turnP`.
-/
structure TemporalEmbedding (Pos : Type) extends TraceGameEmbedding Pos where
  Next : Pos → Pos
  hom : ∀ p, G.moves (embed p) = {embed (Next p)}
  turnP : ∀ p, G.turn (embed p) = Turn.P
  start : Pos

/--
**TimeTrace**: The Trace seen as a function of time (along the orbit).
`TimeTrace emb k` is true if the system halts at step k.
-/
def TimeTrace {Pos : Type} (emb : TemporalEmbedding Pos) : RevHalt.Trace :=
  fun k => emb.T (iterate Pos emb.Next k emb.start)

/--
**Theorem: Stabilization Chain Orbit.**
The orbital form of protection: nothing on the orbit halts.
-/
theorem stabilization_chain_orbit
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : ∀ k, ¬ emb.T (iterate Pos emb.Next k emb.start) := by
  intro k
  -- 1. Orbit Closure of Queue (Queue is invariant)
  have hQ_k : Queue Pos emb.Next S d I0 (iterate Pos emb.Next k emb.start) :=
    queue_orbit_closed Pos emb.Next S d I0 emb.start hQ k

  -- 2. Apply Hierarchy Chain to the k-th point
  apply hierarchy_chain
      Pos S d I0 emb.Next
      emb.toTraceGameEmbedding
      emb.hom
      emb.turnP
      h_safe
      (iterate Pos emb.Next k emb.start)
      hQ_k

/--
**Theorem: Full Stabilization (Up1).**
If the start is covered by a Queue, then the TimeTrace Stabilizes.
This is the final RevHalt statement: `Stabilizes (TimeTrace emb)`.
-/
theorem stabilization_chain_up1
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : RevHalt.Stabilizes (TimeTrace emb) := by
  -- Definition of Stabilizes is ∀ k, ¬ TimeTrace emb k
  intro k
  exact stabilization_chain_orbit Pos S d I0 emb h_safe hQ k

end RevHalt.Hierarchy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6. Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

namespace RevHalt.Hierarchy
#print axioms avoid2_implies_not_target
#print axioms up2_implies_up1_pointwise
#print axioms splitter_implies_avoid2
#print axioms hierarchy_chain
#print axioms stabilization_chain_up1
end RevHalt.Hierarchy
