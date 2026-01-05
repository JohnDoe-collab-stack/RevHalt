import RevHalt.Theory.Splitter
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic

namespace RevHalt.Splitter.Arithmetic

-- Do not open RevHalt.Splitter to avoid ambiguity with namespace vs structure

/-- Modulo constraint: n ≡ r (mod m). -/
def ModConstraint (m r : ℕ) : RevHalt.Splitter.Constraint ℕ := fun n => n % m = r

/-- Splitter based on modulo m. Requires m > 0. -/
def SplitMod (m : ℕ) (hm : m > 0) : RevHalt.Splitter.Splitter ℕ :=
  let split_fn (I : RevHalt.Splitter.Info ℕ) := (List.range m).map (fun r => I ++ [ModConstraint m r])
  {
    split := split_fn

    refinement := by
      intro I J hJ n hSatJ
      have hSp : split_fn I = (List.range m).map (fun r => I ++ [ModConstraint m r]) := rfl
      rw [hSp] at hJ
      simp only [List.mem_map] at hJ
      obtain ⟨r, _, hr⟩ := hJ
      rw [← hr] at hSatJ
      intro c hc
      apply hSatJ c
      apply List.mem_append_left
      exact hc

    cover := by
      intro I n hSatI
      let r := n % m
      have hr : r < m := Nat.mod_lt n hm
      let J := I ++ [ModConstraint m r]
      refine ⟨J, ?_, ?_⟩
      · dsimp [split_fn]
        simp only [List.mem_map]
        refine ⟨r, List.mem_range.mpr hr, rfl⟩
      · intro c hc
        rw [List.mem_append] at hc
        cases hc with
        | inl hInI => exact hSatI c hInI
        | inr hEq =>
            simp only [List.mem_singleton] at hEq
            rw [hEq]
            rfl
  }

/-- SplitFamily for natural numbers. Maps 0 and 1 to a trivial splitter. -/
def SplitFamily (p : ℕ) : RevHalt.Splitter.Splitter ℕ :=
  if hp : p > 0 then SplitMod p hp else
    -- Fallback for 0
    { split := fun I => [I],
      refinement := by
        intro I J hJ n hSat
        simp only [List.mem_singleton] at hJ
        rw [hJ] at hSat
        exact hSat
      cover := fun I n h => ⟨I, List.mem_singleton.mpr rfl, h⟩ }

/-- Prime_RH definition using SplitFamily. -/
def Prime_RH_Arith (p : ℕ) : Prop := RevHalt.Splitter.Prime_RH SplitFamily p

theorem prime_iff_atomic (p : ℕ) (hp : p ≥ 2) :
    Prime_RH_Arith p ↔ Nat.Prime p := by
  sorry

end RevHalt.Splitter.Arithmetic
