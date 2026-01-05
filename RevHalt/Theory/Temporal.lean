import RevHalt.Theory.Stabilization
import RevHalt.Theory.Up2
import RevHalt.Theory.Splitter.AvoidanceBridge
import RevHalt.Theory.Splitter.Core

/-!
# RevHalt.Theory.Temporal

This module defines the **Canonical Temporal Interface** for RevHalt.

It formalizes the construction of a temporal trace from a structural dynamical system:
1.  **TemporalSystem**: A system with state evolution (`Next`) embedded into a Game.
2.  **TimeTrace**: The trace `T(k)` synthesized from hitting a `Target` along the orbit.
3.  **Stabilization**: The proof that if the system is covered by arithmetic residues (`Splitter`), the trace stabilizes.

This is the standard interface for applying RevHalt to concrete systems (like Collatz).
-/

namespace RevHalt.Theory

open RevHalt.Splitter
open RevHalt.Up2
open RevHalt.Bridge

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. Canonical Temporal System
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**TemporalSystem**: The canonical structure linking arithmetic dynamics to game theory.
-/
structure TemporalSystem (Pos : Type) where
  /-- The dynamic update function (e.g., Collatz map). -/
  Next : Pos → Pos
  /-- The starting position of the trajectory. -/
  start : Pos
  /-- The abstract Game structure. -/
  G : Game
  /-- Embedding of system states into Game positions. -/
  embed : Pos → G.Pos
  /-- The Target region (e.g., Halting states). -/
  Target : Set G.Pos
  /-- Structural Homomorphism: Game moves must match System dynamics. -/
  hom : ∀ p, G.moves (embed p) = {embed (Next p)}
  /-- Turn Constraint: The system is viewed as Proponent-controlled (deterministic). -/
  turnP : ∀ p, G.turn (embed p) = Turn.P

/--
**TimeTrace**: Synthesizes a RevHalt Trace (`Nat → Prop`) from the system.
`TimeTrace k` is True iff the system hits the Target at step `k`.
-/
def TimeTrace {Pos : Type} (sys : TemporalSystem Pos) : RevHalt.Trace :=
  fun k => sys.embed (iterate Pos sys.Next k sys.start) ∈ sys.Target

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. From Avoidance to Stabilization (Generic)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Lemma**: If a point is in the Infinite Safety Kernel (`Avoid2Set`), it is not in Target.
-/
theorem temporal_avoid2_safe (sys : TemporalSystem Pos) (p : Pos)
    (h : Avoid2Mem sys.G sys.Target (sys.embed p)) :
    sys.embed p ∉ sys.Target := by
  rw [Avoid2Mem, Avoid2Set] at h
  rcases h with ⟨X, hClosed, hpX⟩
  exact (hClosed hpX).1

/--
**Theorem**: If the start is in the Safety Kernel, and the Kernel is closed under dynamics,
then the TimeTrace stabilizes.
-/
theorem temporal_stabilization_abstract
    (Pos : Type) (sys : TemporalSystem Pos)
    (h_inv : ∀ p, Avoid2Mem sys.G sys.Target (sys.embed p) → Avoid2Mem sys.G sys.Target (sys.embed (sys.Next p)))
    (h_start : Avoid2Mem sys.G sys.Target (sys.embed sys.start))
    : RevHalt.Stabilizes (TimeTrace sys) := by
  intro k
  -- By induction (or orbit closure), every point in the orbit is in Avoid2Set
  let orbit_pt (t : ℕ) := iterate Pos sys.Next t sys.start

  have h_safe_k : Avoid2Mem sys.G sys.Target (sys.embed (orbit_pt k)) := by
    induction k with
    | zero => exact h_start
    | succ k ih =>
      -- Explicit unfold of iterate for succ k
      show Avoid2Mem sys.G sys.Target (sys.embed (sys.Next (orbit_pt k)))
      apply h_inv
      exact ih

  -- Avoid2Mem implies not Target implies not TimeTrace
  have h_not_target := temporal_avoid2_safe sys (orbit_pt k) h_safe_k
  exact h_not_target

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. The Constructive Power: Splitter implies Stabilization
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Main Theorem**: `splitter_stabilizes`
If a TemporalSystem is covered by a valid `Queue` splitter,
then it formally stabilizes.

This is the automated "certificate check" for non-halting.
-/
theorem splitter_stabilizes
    (Pos : Type)
    (sys : TemporalSystem Pos)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    -- The Certificate: A valid Queue covering the start
    (hQ : Queue Pos sys.Next S d I0 sys.start)
    -- The Safety Contract: The Splitter guarantees Avoidance locally
    (h_bridge : ∀ p, Queue Pos sys.Next S d I0 p → sys.embed p ∉ sys.Target)
    : RevHalt.Stabilizes (TimeTrace sys) := by

  -- 1. Helper: Any point in orbit is covered by Queue
  intro k
  let pt_k := iterate Pos sys.Next k sys.start

  have hQ_k : Queue Pos sys.Next S d I0 pt_k :=
    queue_orbit_closed Pos sys.Next S d I0 sys.start hQ k

  -- 2. Use the Bridge theorem from AvoidanceBridge to get Avoid2Mem
  have hAvoid : Avoid2Mem sys.G sys.Target (sys.embed pt_k) :=
    queue_splitter_subset_avoid2 Pos S d I0 sys.Next sys.G sys.embed sys.Target
      sys.hom
      sys.turnP
      h_bridge
      pt_k
      hQ_k

  -- 3. Safety: Avoid2Set implies not Target
  have hNotTarget := temporal_avoid2_safe sys pt_k hAvoid

  -- 4. Conclusion
  exact hNotTarget

/--
**Verification Order**:
Explicitly confirm that `Stabilizes` reduces to `∀ n, ¬ T n`.
-/
theorem verification_stabilizes_def (T : Trace) :
    RevHalt.Stabilizes T ↔ ∀ n, ¬ T n := by
  rfl

end RevHalt.Theory

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4. Axiom Verification
-- ═══════════════════════════════════════════════════════════════════════════════

namespace RevHalt.Theory
#print axioms temporal_avoid2_safe
#print axioms temporal_stabilization_abstract
#print axioms splitter_stabilizes
end RevHalt.Theory
