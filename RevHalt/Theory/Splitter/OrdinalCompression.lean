import RevHalt.Theory.Hierarchy
import RevHalt.Theory.Splitter.Core

/-!
# RevHalt.Theory.Splitter.OrdinalCompression

Formalization of the "Ordinal Compression" argument.
Refactored to be **Axiom-Minimal** and **Generalized**.

## The Argument (Grothendieck Style)

1. **Coinduction**: A generic principle that `PostFix C → Safe`.
2. **Compression**: The construction of a `PostFix` witness from a structural `Queue`.
   This relies on a **Simulation** of the finite `Next` by the game's `Moves`.

## Architecture
- **Abstract**: Pure logic (Predicates, Relations). 0 Axioms.
- **Bridge**: Adapts RevHalt's `Game` (Set/Quotient) to the Abstract Relation.

-/

namespace RevHalt.Splitter.OrdinalCompression

open RevHalt.Hierarchy
open RevHalt.Splitter

universe u

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Abstract Fixed Point Theory (Coinduction)
-- ═══════════════════════════════════════════════════════════════════════════════

variable {X : Type u}
variable (Moves : X → X → Prop) -- Transition relation (possibly non-deterministic)
variable (Target : X → Prop)    -- Target predicate

/-- The safety operator: G(S) = {x | ¬ Target x ∧ ∀ y, Moves x y → S y}. -/
def G (S : X → Prop) : X → Prop :=
  fun x => ¬ Target x ∧ ∀ y, Moves x y → S y

/-- Post-fixed point (invariant) certificate. -/
def PostFix (C : X → Prop) : Prop :=
  ∀ x, C x → G Moves Target C x

/-- Reachability relation (Reflexive Transitive Closure). -/
inductive Reachable (x : X) : X → Prop
  | refl : Reachable x x
  | step : ∀ y z, Reachable x y → Moves y z → Reachable x z

/-- Greatest fixpoint safety property. "Safe for all future reachable states". -/
def Safe (x : X) : Prop := ∀ y, Reachable Moves x y → ¬ Target y

/-- Helper: Invariant implies all reachable points are in Invariant. -/
theorem postFix_imp_reachable_subset (C : X → Prop) (hC : PostFix Moves Target C) :
    ∀ x, C x → ∀ y, Reachable Moves x y → C y := by
  intro x hx y hReach
  induction hReach with
  | refl => exact hx
  | step y z _ h_y_z ih_y =>
      exact (hC y ih_y).2 z h_y_z

/--
**Theorem: Coinduction Principle.**
If `C` is a post-fixed point of `G`, then any start state in `C` is Safe.
-/
theorem Coinduction (C : X → Prop) (hC : PostFix Moves Target C) :
    ∀ x, C x → Safe Moves Target x := by
  intro x hx y hReach
  have hy : C y := postFix_imp_reachable_subset Moves Target C hC x hx y hReach
  exact (hC y hy).1

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) The Compression Theorem (Abstract Simulation)
-- ═══════════════════════════════════════════════════════════════════════════════

section AbstractCompression

variable (Pos : Type) (World : Type)
variable (Next : Pos → Pos)
variable (Rel : World → World → Prop) -- Abstract Transition Relation
variable (Bad : World → Prop)         -- Abstract Target/Bad Predicate
variable (embed : Pos → World)
variable (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)

/-- The Structural Invariant C constructed from the Queue. -/
def QueueInvariant : World → Prop :=
  fun x => ∃ p, Queue Pos Next S d I0 p ∧ x = embed p

/--
**Theorem: Compression.**
The structural `Queue` induces a Post-Fixed Point (Invariant) in the World dynamics.

Hypotheses:
1. `h_safe`: The Queue is safe relative to the Target mapping.
2. `h_sim`: Weak functional simulation. `Rel` in the World follows `Next` in Pos.
            (Relaxed from ↔ to →: we only need to know that transitions stay in the image).
-/
theorem Compression
    (h_safe : ∀ p, Queue Pos Next S d I0 p → ¬ Bad (embed p))
    (h_sim : ∀ p y, Rel (embed p) y → y = embed (Next p))
    : PostFix Rel Bad (QueueInvariant Pos World Next embed S d I0) := by
  intro x hx
  rcases hx with ⟨p, hQ, hx_eq⟩
  rw [hx_eq]
  constructor
  · -- 1. Not Target
    exact h_safe p hQ
  · -- 2. All successors are in QueueInvariant
    intro y hy_moves
    -- Use weak simulation to locate y
    have h_y_eq : y = embed (Next p) := h_sim p y hy_moves
    rw [h_y_eq]
    -- Queue is closed under Next (Internal structure)
    have hQ_next : Queue Pos Next S d I0 (Next p) :=
      RevHalt.Splitter.queue_orbit_closed Pos Next S d I0 p hQ 1
    exact ⟨Next p, ⟨hQ_next, rfl⟩⟩

end AbstractCompression

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Concrete Instantiation (The Bridge)
-- ═══════════════════════════════════════════════════════════════════════════════

section ConcreteBridge

variable (Pos : Type)
variable (emb : TemporalEmbedding Pos)
variable (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)

/-- Concrete Moves relation derived from the Game. -/
def EmbMoves : emb.G.Pos → emb.G.Pos → Prop :=
  fun x y => y ∈ emb.G.moves x

/-- Concrete Target predicate derived from the Game. -/
def EmbTarget : emb.G.Pos → Prop :=
  fun x => x ∈ emb.Target

/--
**Bridge Lemma**: RevHalt's Game structure satisfies Weak Simulation.
This isolates `Set` membership and `Quotient` equality axioms.
-/
theorem concrete_simulation (p : Pos) (y : emb.G.Pos) :
    EmbMoves Pos emb (emb.embed p) y → y = emb.embed (emb.Next p) := by
  -- Unfold EmbMoves
  intro h
  change y ∈ emb.G.moves (emb.embed p) at h
  -- Apply Homomorphism: moves = {next}
  rw [emb.hom p] at h
  -- Set membership to equality (The Axiom/Mathlib Bridge)
  exact Set.mem_singleton_iff.mp h

/--
**Theorem: Ordinal Compression (Final)**.
Application of Compression + Coinduction to the RevHalt system.
-/
theorem ordinal_compression
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ_start : Queue Pos emb.Next S d I0 emb.start)
    : Safe (EmbMoves Pos emb) (EmbTarget Pos emb) (emb.embed emb.start) := by
  -- 1. Construct the Invariant C
  let C := QueueInvariant Pos emb.G.Pos emb.Next emb.embed S d I0

  -- 2. "Compression": Prove C is a post-fixpoint via weak simulation
  have hPost : PostFix (EmbMoves Pos emb) (EmbTarget Pos emb) C :=
    Compression
      Pos emb.G.Pos emb.Next (EmbMoves Pos emb) (EmbTarget Pos emb) emb.embed S d I0
      h_safe
      (concrete_simulation Pos emb)

  -- 3. "Coinduction": Safety
  apply Coinduction (EmbMoves Pos emb) (EmbTarget Pos emb) C hPost

  -- 4. Start condition
  exact ⟨emb.start, ⟨hQ_start, rfl⟩⟩

end ConcreteBridge

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Axiom Audit
-- ═══════════════════════════════════════════════════════════════════════════════

namespace RevHalt.Splitter.OrdinalCompression
-- Pure Logic: 0 Axioms
#print axioms G
#print axioms PostFix
#print axioms Safe
#print axioms Coinduction
#print axioms Compression -- 0 Axioms verified

-- Bridge: propext + Quot.sound (from Game, unavoidable)
#print axioms concrete_simulation

-- Final Theorem: inherits Bridge axioms
#print axioms ordinal_compression
end RevHalt.Splitter.OrdinalCompression
