import RevHalt.Theory.Splitter.Core
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Theory.Splitter.Mod

Modulo-based splitters (axiom-free).

This is the minimal `SplitMod` construction used to split an info-state `I` into the finitely many
residue cases `I ++ [n % m = r]` for `r < m`.
-/

namespace RevHalt.Splitter.Mod

open RevHalt.Splitter

/-- Modulo constraint: `n % m = r`. -/
def ModConstraint (m r : ℕ) : Constraint ℕ := fun n => n % m = r

/-- Splitter by residue modulo `m` (requires `m > 0`). -/
def SplitMod (m : ℕ) (hm : m > 0) : Splitter ℕ :=
  let splitFn (I : Info ℕ) := (List.range m).map (fun r => I ++ [ModConstraint m r])
  {
    split := splitFn
    refinement := by
      intro I J hJ n hSatJ
      simp only [splitFn, List.mem_map] at hJ
      obtain ⟨r, _, hr⟩ := hJ
      rw [← hr] at hSatJ
      intro c hc
      apply hSatJ c
      exact List.mem_append_left _ hc
    cover := by
      intro I n hSatI
      let r := n % m
      have hr : r < m := Nat.mod_lt n hm
      let J := I ++ [ModConstraint m r]
      refine ⟨J, ?_, ?_⟩
      · simp only [splitFn, List.mem_map]
        refine ⟨r, ?_, rfl⟩
        exact List.mem_range.mpr hr
      · intro c hc
        rw [List.mem_append] at hc
        cases hc with
        | inl hInI =>
            exact hSatI c hInI
        | inr hEq =>
            simp only [List.mem_singleton] at hEq
            subst hEq
            rfl
  }

end RevHalt.Splitter.Mod

