import Mathlib.Data.Set.Basic
example {α : Type} (a : α) : a ∈ (Set.singleton a : Set α) := by
  simp [Set.singleton]
