import RevHalt.Theory.Collatz
import RevHalt.Theory.Splitter.Bridge
import RevHalt.Theory.Splitter.Mod

/-!
# RevHalt.Theory.CollatzBridge

Small bridge example: package a concrete Collatz fact (`n % 8 = 5` gives a high-gain 1-step window)
as a `Splitter`-style `WinningCase`, and feed it to `Splitter_implies_Win`.

This shows how the Collatz “certificate” layer plugs into the generic Splitter→Up2Gain bridge.
-/

namespace RevHalt.Collatz

open RevHalt.Splitter
open RevHalt.Bridge
open RevHalt.Up2Gain
open RevHalt.Splitter.Mod

/-- Info-state encoding the residue class `n % 8 = 5`. -/
def I_mod8_eq5 : Info ℕ := [fun n => n % 8 = 5]

theorem sat_I_mod8_eq5_iff (n : ℕ) : Sat ℕ I_mod8_eq5 n ↔ n % 8 = 5 := by
  simp [I_mod8_eq5, Sat]

theorem winningCase_I_mod8_eq5 : WinningCase I_mod8_eq5 := by
  intro n hSat
  have hn : n % 8 = 5 := (sat_I_mod8_eq5_iff n).1 hSat
  rcases oneStepWindow_highGain_of_mod8_eq5 (n := n) hn with ⟨hW, hGain⟩
  refine ⟨1, tag n, shortcut n, hW, ?_⟩
  simpa using hGain

/-- Semantic payoff: any `WinningCase` gives a genuine descent step (`m < n`) when `n ≥ 1`. -/
theorem winningCase_implies_descent {J : Info ℕ} (hWin : WinningCase J) {n : ℕ}
    (hSat : Sat ℕ J n) (hn : 1 ≤ n) :
    ∃ L g m, Window L n g m ∧ g ≥ 2 * L + 1 ∧ m < n := by
  rcases hWin n hSat with ⟨L, g, m, hW, hG⟩
  refine ⟨L, g, m, hW, hG, ?_⟩
  exact window_highGain_implies_lt (L := L) (n := n) (g := g) (m := m) hn hW hG

/--
Concrete bridge output (Up2Gain): if `n % 8 = 5` then `Ask n` is winning, for any base predicate `B`.

We use `d = 0` so `Cases` is just `[I_mod8_eq5]`; the only obligation is the `WinningCase` proof above.
-/
theorem up2mem_ask_of_mod8_eq5 (B : ℕ → Prop) {n : ℕ} (hn : n % 8 = 5) :
    Up2Mem B (Pos.Ask n) := by
  refine
    Splitter_implies_Win
      (S := IdSplitter ℕ)
      (d := 0)
      (I := I_mod8_eq5)
      (n := n)
      (B := B)
      ?_ ?_
  · -- `Sat I_mod8_eq5 n`
    simpa [sat_I_mod8_eq5_iff] using hn
  · -- All `Cases` (only one) are winning cases
    intro J hJ
    simp [Cases, I_mod8_eq5] at hJ
    subst hJ
    exact winningCase_I_mod8_eq5

/-!
## The “table” pattern (what a full Collatz proof would need)

If you can supply a `WinningCase` for *every* residue class modulo 8, then splitting on `n % 8`
is enough to feed the bridge and obtain `Up2Mem B (Ask n)` for all `n`.

The point: the only “hard” content is the finite family of per-residue certificates.
-/

/-- Info-state for a fixed residue class modulo 8. -/
def I_mod8 (r : ℕ) : Info ℕ := [ModConstraint 8 r]

theorem up2mem_ask_of_mod8_table (B : ℕ → Prop)
    (hWin : ∀ r : ℕ, r < 8 → WinningCase (I_mod8 r)) :
    ∀ n : ℕ, Up2Mem B (Pos.Ask n) := by
  intro n
  let S : Splitter ℕ := SplitMod 8 (by decide : 0 < 8)
  refine
    Splitter_implies_Win
      (S := S)
      (d := 1)
      (I := ([] : Info ℕ))
      (n := n)
      (B := B)
      (by simpa [Sat])
      ?_
  intro J hJ
  -- `Cases 1 [] = S.split []`, and each case is `I_mod8 r` for some `r < 8`.
  have hJ' : J ∈ S.split ([] : Info ℕ) := by
    simpa [S, Cases] using hJ
  simp [S, SplitMod, I_mod8, ModConstraint] at hJ'
  rcases hJ' with ⟨r, hr, rfl⟩
  exact hWin r hr

end RevHalt.Collatz
