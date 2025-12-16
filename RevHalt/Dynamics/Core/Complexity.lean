/-
  RevHalt.Dynamics.Core.Complexity

  Computable Complexity: Cost of paths in the axiom graph.

  Philosophy:
  - No `sInf` or `sSup` on infinite sets
  - No `noncomputable`
  - Cost is a recursive function on the Path structure
  - Theorems express structural bounds, not optimal minima
-/

import RevHalt.Dynamics.Core.Path
import Mathlib.Data.Nat.Basic

namespace RevHalt.Dynamics.Core.Complexity

open RevHalt.Dynamics.Core

variable {Code PropT : Type}
variable {ctx : EnrichedContext Code PropT}

/-!
  ## 1. Move Cost (Computable)

  Each move has an intrinsic cost. This is a design choice:
  - `extend`: standard deduction, costs 1
  - `extend_gap`: extracting gap information, also costs 1

  In a more refined model, we could weight these differently.
-/

/-- Cost of a single move. Computable. -/
def moveCost (m : Move ctx) : ℕ :=
  match m with
  | .extend _ _ => 1
  | .extend_gap _ => 1

/-- All moves have positive cost. -/
theorem moveCost_pos (m : Move ctx) : 0 < moveCost m := by
  cases m <;> simp [moveCost]

/-!
  ## 2. Path Cost (Computable by Structural Recursion)

  The cost of a path is the sum of its move costs.
  This is a total computable function.
-/

/-- Total cost of a path. Computable by structural recursion. -/
def pathCost : Path ctx T T' → ℕ
  | .nil _ => 0
  | .step m _ tail => moveCost m + pathCost tail

/-- Cost of nil path is zero. -/
@[simp] theorem pathCost_nil (T : TheoryNode ctx) : pathCost (Path.nil T) = 0 := rfl

/-- Cost of single-move path equals move cost. -/
theorem pathCost_of_move (m : Move ctx) (T : TheoryNode ctx) :
    pathCost (Path.of_move m T) = moveCost m := by
  simp [Path.of_move, pathCost]

/-- Cost is additive under concatenation. -/
theorem pathCost_concat (p : Path ctx T T') (q : Path ctx T' T'') :
    pathCost (p.concat q) = pathCost p + pathCost q := by
  induction p with
  | nil _ => simp [Path.concat, pathCost]
  | step m T tail ih =>
    simp only [Path.concat, pathCost]
    rw [ih]
    omega

/-!
  ## 3. Cost vs Length

  With uniform costs (all moves cost 1), cost equals length.
  This is a structural invariant, not an optimization.
-/

/-- With uniform costs, pathCost = length. -/
theorem pathCost_eq_length (p : Path ctx T T') : pathCost p = p.length := by
  induction p with
  | nil _ => simp [pathCost, Path.length]
  | step m T tail ih =>
    simp only [pathCost, Path.length]
    rw [ih]
    cases m <;> simp only [moveCost, Nat.add_comm]

/-- Corollary: path cost is always non-negative (trivial but stated). -/
theorem pathCost_nonneg (p : Path ctx T T') : 0 ≤ pathCost p := Nat.zero_le _

/-!
  ## 4. Monotonicity of Cost

  Longer paths cost more. This is the "no free lunch" principle.
-/

/-- Prefix path has smaller cost. -/
theorem pathCost_le_concat_left (p : Path ctx T T') (q : Path ctx T' T'') :
    pathCost p ≤ pathCost (p.concat q) := by
  rw [pathCost_concat]
  omega

/-- Suffix path has smaller cost. -/
theorem pathCost_le_concat_right (p : Path ctx T T') (q : Path ctx T' T'') :
    pathCost q ≤ pathCost (p.concat q) := by
  rw [pathCost_concat]
  omega

/-!
  ## 5. Complexity Certification

  The key theorem: if a path witnesses some property,
  its cost is a certified upper bound on the complexity of that property.

  Unlike Kolmogorov complexity (which seeks the minimum over all programs),
  this is a **witness complexity**: the cost of the specific path we have.
-/

/-- A certified complexity witness for a target theory. -/
structure ComplexityCertificate (ctx : EnrichedContext Code PropT) where
  source : TheoryNode ctx
  target : TheoryNode ctx
  path : Path ctx source target
  cost : ℕ
  cost_eq : cost = pathCost path

/-- Construct a certificate from a path. -/
def certify (p : Path ctx T T') : ComplexityCertificate ctx where
  source := T
  target := T'
  path := p
  cost := pathCost p
  cost_eq := rfl

/-- The certificate cost is computable. -/
theorem certificate_cost_computable (c : ComplexityCertificate ctx) :
    c.cost = pathCost c.path := c.cost_eq

/-!
  ## 6. Information-Theoretic Bound (Abstract)

  This is the key structural theorem.
  We state it abstractly: if a path "witnesses n bits of information",
  then its cost is at least n.

  The concrete instantiation will be in the Omega module,
  where "n bits" means "precision 2^{-n} on Ω".
-/

/-- An information gain measure on paths.
    Concrete instances defined elsewhere (e.g., for Ω precision).

    Required properties:
    - `gain_nil`: empty path contributes 0 information
    - `gain_subadditive`: concatenation doesn't exceed sum of gains -/
class InfoGain (ctx : EnrichedContext Code PropT) where
  gain : {T T' : TheoryNode ctx} → Path ctx T T' → ℕ
  gain_nil : ∀ T : TheoryNode ctx, gain (Path.nil T) = 0
  gain_step : ∀ (m : Move ctx) (T : TheoryNode ctx) (tail : Path ctx (Move.apply m T) T'),
    gain (Path.step m T tail) ≤ gain (Path.of_move m T) + gain tail

/-- Information-theoretic lower bound: cost ≥ information gained.
    This is the abstract form; concrete proofs depend on the domain. -/
theorem cost_ge_info_gain
    [ig : InfoGain ctx] (p : Path ctx T T')
    (h_yield : ∀ (m : Move ctx) (T : TheoryNode ctx), ig.gain (Path.of_move m T) ≤ moveCost m) :
    ig.gain p ≤ pathCost p := by
  induction p with
  | nil T =>
    simp only [ig.gain_nil, pathCost_nil, le_refl]
  | step m T tail ih =>
    calc ig.gain (Path.step m T tail)
        ≤ ig.gain (Path.of_move m T) + ig.gain tail := ig.gain_step m T tail
      _ ≤ moveCost m + ig.gain tail := Nat.add_le_add_right (h_yield m T) _
      _ ≤ moveCost m + pathCost tail := Nat.add_le_add_left ih _
      _ = pathCost (Path.step m T tail) := by simp [pathCost]

end RevHalt.Dynamics.Core.Complexity
