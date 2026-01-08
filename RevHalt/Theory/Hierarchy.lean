import RevHalt.Theory.Stabilization
import RevHalt.Theory.Up2
import RevHalt.Theory.Splitter.AvoidanceBridge
import RevHalt.Theory.Splitter.Core
import RevHalt.Theory.Categorical
import RevHalt.Theory.Temporal

/-!
# RevHalt.Theory.Hierarchy

This module serves as the **unification layer** for the RevHalt theory components:

10:
11: 1.  **Up1 (Stabilization)**: Temporal safety (Pi-1). "Never Halts".
12:         Up1 is exported both as Pi-1 (`Stabilizes`) and as the kernel condition `up(TimeTrace)=bot` (equivalently membership in `upKernel`).
13: 2.  **Up2 (Avoidance)**: Structural safety (Pi-2). "Winning Strategy to avoid Halting".
14: 3.  **Splitter (Resolution)**: Arithmetic safety. "Resolvable into stable Prime components".

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
Up2 (along the orbit) implies Up1 (logical form).

If every state on the deterministic orbit belongs to the Avoid2-kernel,
then the induced TimeTrace stabilizes (never hits the target).
-/
theorem up2_orbit_implies_stabilizes
    (Pos : Type)
    (emb : TemporalEmbedding Pos)
    (hAvoid_orbit :
      ∀ k, Avoid2Mem emb.G emb.Target
            (emb.embed (iterate Pos emb.Next k emb.start)))
    : RevHalt.Stabilizes (TimeTrace emb) := by
  intro k
  have hpoint :
      ¬ emb.toTraceGameEmbedding.T (iterate Pos emb.Next k emb.start) :=
    up2_implies_up1_pointwise
      (emb := emb.toTraceGameEmbedding)
      (n := iterate Pos emb.Next k emb.start)
      (hAvoid := hAvoid_orbit k)
  simpa [TimeTrace] using hpoint

/--
Up2 (along the orbit) implies Up1 (operative/kernel form).

Same as `up2_orbit_implies_stabilizes`, but exported as `up (TimeTrace emb) = ⊥`.
-/
theorem up2_orbit_implies_upEqBot
    (Pos : Type)
    (emb : TemporalEmbedding Pos)
    (hAvoid_orbit :
      ∀ k, Avoid2Mem emb.G emb.Target
            (emb.embed (iterate Pos emb.Next k emb.start)))
    : RevHalt.up (TimeTrace emb) = (⊥ : RevHalt.Trace) := by
  have hstab : RevHalt.Stabilizes (TimeTrace emb) :=
    up2_orbit_implies_stabilizes (Pos := Pos) emb hAvoid_orbit
  exact (RevHalt.Stabilizes_iff_up_eq_bot (T := TimeTrace emb)).1 hstab

/--
Queue/Splitter (with local safety) implies Up2 along the deterministic orbit.
-/
theorem queue_implies_up2_orbit
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : ∀ k, Avoid2Mem emb.G emb.Target
            (emb.embed (iterate Pos emb.Next k emb.start)) := by
  intro k
  have hQ_k : Queue Pos emb.Next S d I0 (iterate Pos emb.Next k emb.start) :=
    queue_orbit_closed Pos emb.Next S d I0 emb.start hQ k
  -- apply the bridge at the k-th point
  exact splitter_implies_avoid2
    Pos S d I0 emb.Next
    emb.G emb.embed emb.Target
    emb.hom emb.turnP
    h_safe
    (iterate Pos emb.Next k emb.start)
    hQ_k

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
  -- Composition: Queue -> Up2 (orbit) -> Up1 (Trace) -> Pointwise
  have hAvoidOrbit := queue_implies_up2_orbit Pos S d I0 emb h_safe hQ
  have hStab := up2_orbit_implies_stabilizes Pos emb hAvoidOrbit
  intro k
  exact (Theory.verification_stabilizes_def _).mp hStab k

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
    : RevHalt.Stabilizes (TimeTrace emb) :=
  -- Direct composition: Queue -> Up2 (orbit) -> Up1
  up2_orbit_implies_stabilizes (Pos := Pos) emb
    (queue_implies_up2_orbit Pos S d I0 emb h_safe hQ)

/-- Up1 (operative form): the TimeTrace lies in the kernel of `up`. -/
theorem stabilization_chain_up1_upEqBot
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : RevHalt.up (TimeTrace emb) = (⊥ : RevHalt.Trace) := by
  have hstab : RevHalt.Stabilizes (TimeTrace emb) :=
    stabilization_chain_up1 Pos S d I0 emb h_safe hQ
  -- Stabilizes T -> up T = ⊥
  exact (RevHalt.Stabilizes_iff_up_eq_bot (T := TimeTrace emb)).mp hstab

/-- Same statement, as kernel membership (categorical view). -/
theorem stabilization_chain_up1_mem_upKernel
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : (TimeTrace emb) ∈ RevHalt.Categorical.upKernel := by
  -- upKernel := {T | upOp T = ⊥}
  simpa [RevHalt.Categorical.upKernel, RevHalt.Categorical.upOp] using
    (stabilization_chain_up1_upEqBot Pos S d I0 emb h_safe hQ)

end RevHalt.Hierarchy

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6. Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

namespace RevHalt.Hierarchy
#print axioms avoid2_implies_not_target
#print axioms up2_implies_up1_pointwise
#print axioms splitter_implies_avoid2
#print axioms hierarchy_chain
#print axioms queue_implies_up2_orbit
#print axioms stabilization_chain_up1
#print axioms stabilization_chain_up1_upEqBot
#print axioms stabilization_chain_up1_mem_upKernel
#print axioms up2_orbit_implies_upEqBot
#print axioms up2_orbit_implies_stabilizes
end RevHalt.Hierarchy
