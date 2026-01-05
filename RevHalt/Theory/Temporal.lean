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

-- Robust simp lemmas for iterate (Option B)
@[simp] lemma iterate_zero {Pos : Type} (Next : Pos → Pos) (start : Pos) :
  iterate Pos Next 0 start = start := by
  rfl

@[simp] lemma iterate_succ {Pos : Type} (Next : Pos → Pos) (k : ℕ) (start : Pos) :
  iterate Pos Next (k+1) start = Next (iterate Pos Next k start) := by
  rfl

structure TemporalSystem (Pos : Type) where
  Next   : Pos → Pos
  start  : Pos
  G      : Game
  embed  : Pos → G.Pos
  Target : Set G.Pos
  hom    : ∀ p, G.moves (embed p) = {embed (Next p)}
  turnP  : ∀ p, G.turn (embed p) = Turn.P

def TimeTrace {Pos : Type} (sys : TemporalSystem Pos) : RevHalt.Trace :=
  fun k => sys.embed (iterate Pos sys.Next k sys.start) ∈ sys.Target

theorem temporal_avoid2_safe {Pos : Type} (sys : TemporalSystem Pos) (p : Pos)
    (h : Avoid2Mem sys.G sys.Target (sys.embed p)) :
    sys.embed p ∉ sys.Target := by
  rw [Avoid2Mem, Avoid2Set] at h
  rcases h with ⟨X, hClosed, hpX⟩
  exact (hClosed hpX).1

theorem temporal_stabilization_abstract
    {Pos : Type} (sys : TemporalSystem Pos)
    (h_inv : ∀ p,
      Avoid2Mem sys.G sys.Target (sys.embed p) →
      Avoid2Mem sys.G sys.Target (sys.embed (sys.Next p)))
    (h_start : Avoid2Mem sys.G sys.Target (sys.embed sys.start)) :
    RevHalt.Stabilizes (TimeTrace sys) := by
  intro k
  let orbit_pt : ℕ → Pos := fun t => iterate Pos sys.Next t sys.start

  have h_safe_k : Avoid2Mem sys.G sys.Target (sys.embed (orbit_pt k)) := by
    induction k with
    | zero =>
        simpa [orbit_pt, iterate_zero]
          using h_start
    | succ k ih =>
        -- robust: use the local iterate_succ lemmas
        simpa [orbit_pt, iterate_succ]
          using h_inv (orbit_pt k) ih

  have h_not_target := temporal_avoid2_safe sys (orbit_pt k) h_safe_k
  exact h_not_target

theorem splitter_stabilizes
    {Pos : Type}
    (sys : TemporalSystem Pos)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (hQ : Queue Pos sys.Next S d I0 sys.start)
    (h_bridge : ∀ p, Queue Pos sys.Next S d I0 p → sys.embed p ∉ sys.Target) :
    RevHalt.Stabilizes (TimeTrace sys) := by
  intro k
  let pt_k := iterate Pos sys.Next k sys.start

  have hQ_k : Queue Pos sys.Next S d I0 pt_k :=
    queue_orbit_closed Pos sys.Next S d I0 sys.start hQ k

  have hAvoid : Avoid2Mem sys.G sys.Target (sys.embed pt_k) :=
    queue_splitter_subset_avoid2 Pos S d I0 sys.Next sys.G sys.embed sys.Target
      sys.hom sys.turnP h_bridge pt_k hQ_k

  have hNotTarget := temporal_avoid2_safe sys pt_k hAvoid
  exact hNotTarget

theorem verification_stabilizes_def (T : RevHalt.Trace) :
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
