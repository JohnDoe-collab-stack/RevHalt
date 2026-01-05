import RevHalt.Theory.Splitter.Core
import RevHalt.Theory.Up2Gain

/-!
# RevHalt.Theory.SplitterBridge

This module bridges the **Arithmetic Splitter** framework to the **Up2Gain** Game.
It formalizes the principle:
"If a finite observation (Splitter) reveals a Certification (Window) for every case,
 then the initial position is Winning (Up2Set)."

## Main Theorem
`Splitter_implies_Win`: If `Cases(d, I)` covers `n`, and every case in `Cases` implies a valid High-Gain Window, then `n ∈ Up2Set`.
-/

namespace RevHalt.Bridge

open RevHalt.Splitter
open RevHalt.Up2Gain

/-- A Case J is a "Winning Case" if every number satisfying J has a high-gain window. -/
def WinningCase (J : Info ℕ) : Prop :=
  ∀ n, Sat ℕ J n → ∃ L g m, Window L n g m ∧ g ≥ 2 * L + 1

/-- The Bridge Theorem: Finite Splitting + Certificate = Strategy. -/
theorem Splitter_implies_Win
    (S : Splitter ℕ)
    (d : ℕ)
    (I : Info ℕ)
    (n : ℕ)
    (B : ℕ → Prop)
    (hSat : Sat ℕ I n)
    (hWin : ∀ J ∈ Cases ℕ S d I, WinningCase J)
    : Up2Mem B (Pos.Ask n) := by
  -- 1. Apply coverage: n is in some case J
  obtain ⟨J, hJ_in_Cases, hSatJ⟩ := RevHalt.Splitter.cases_cover ℕ S d I n hSat

  -- 2. This case J is a Winning Case
  have hWinningJ := hWin J hJ_in_Cases

  -- 3. J implies a Window for n
  obtain ⟨L, g, m, hWindow, hGain⟩ := hWinningJ n hSatJ

  -- 4. Construct winning strategy in Up2Gain
  -- The game allows "ProvideWin" move if a Window exists.
  -- P can move Ask n -> ProvideWin ...
  -- And ProvideWin is a "Good" position (if g is high enough), so it satisfies Up2Mem.

  -- We need to show Pos.Ask n is in Up2Mem.
  -- Up2Mem is the intersection of all Up2Closed sets S.
  -- So we need to show that for any S, Up2Closed B S → S (Ask n).
  intro PropS hClosed
  rcases hClosed with ⟨hSuccess, hP_closed, hO_closed⟩

  -- P can move from Ask n.
  -- Is there a move to ProvideWin?
  -- pCanMove (Ask n) q means q = Step n.
  -- Wait, looking at Up2Gain:
  --   | Pos.Ask n => q = Pos.Step n
  --   | Pos.Step n => q = Ask (shortcut) OR q = ProvideWin ...

  -- So P moves Ask n -> Step n.
  -- Then Step n -> ProvideWin.

  have hStepn : PropS (Pos.Step n) := by
    -- We need to show PropS (Step n).
    -- Turn is P. P can move to ProvideWin.
    apply hP_closed (Pos.Step n) rfl
    -- Show exists q, pCanMove Step n q ∧ PropS q
    use Pos.ProvideWin L n g m
    constructor
    · -- Move valid?
      -- pCanMove Step n q means q = Ask (shortcut) OR q = ProvideWin ...
      right
      use L, g, m
    · -- Show PropS (ProvideWin ...)
      -- Use hSuccess
      apply hSuccess
      right -- isGood
      simp [isGood, hWindow, hGain]

  -- Now show PropS (Ask n) using hStepn
  apply hP_closed (Pos.Ask n) rfl
  use Pos.Step n
  constructor
  · rfl -- Ask n -> Step n is valid
  · exact hStepn

end RevHalt.Bridge

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks (Exhaustive)
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Bridge.WinningCase
#print axioms RevHalt.Bridge.Splitter_implies_Win
