import RevHalt
import Mathlib.Data.Nat.Basic

/-!
# RevComplexity: Time-Bounded Halting and Complexity Classes

This module adds a **time complexity** layer on top of the RevHalt framework.

Core idea:
* We stay in the world of `Trace := ℕ → Prop` and `Halts T := ∃ n, T n`.
* We introduce "halts in time ≤ t".
* We define abstract complexity classes P and NP in terms of
  time-bounded halting controlled by polynomial bounds.

No new axioms are introduced.
-/

namespace RevComplexity

/-- Reuse core RevHalt definitions. -/
abbrev Trace := ℕ → Prop
def Halts (T : Trace) : Prop := ∃ n, T n

/-! ## 1. Time-Bounded Halting -/

/--
`HaltsInTime T t` means "T becomes true at some time n ≤ t".
This is a purely propositional notion, without computing the minimal time.
-/
def HaltsInTime (T : Trace) (t : ℕ) : Prop :=
  ∃ n, n ≤ t ∧ T n

/-- Monotonicity in time: if T halts in time ≤ t₁ and t₁ ≤ t₂, then T halts in time ≤ t₂. -/
lemma HaltsInTime_mono {T : Trace} {t₁ t₂ : ℕ}
    (h_le : t₁ ≤ t₂) :
    HaltsInTime T t₁ → HaltsInTime T t₂ := by
  intro ⟨n, hn_le, hn_T⟩
  exact ⟨n, Nat.le_trans hn_le h_le, hn_T⟩

/-- If T halts in time ≤ t, then T halts (unbounded). -/
lemma Halts_of_HaltsInTime {T : Trace} {t : ℕ} :
    HaltsInTime T t → Halts T := by
  intro ⟨n, _, hn_T⟩
  exact ⟨n, hn_T⟩

/-! ## 2. Languages and Deciders in Trace Terms -/

/-- A language over an input type `α` is simply a predicate. -/
abbrev Lang (α : Type) := α → Prop

/--
`DecidesLang T L` means:
  For all `x`, `T x` halts if and only if `x` is in `L`.

In other words, `T` is an exact decider for `L` in the Rev world:
* If `L x` is true, then `T x` halts.
* If `L x` is false, then `T x` never halts.
-/
def DecidesLang {α : Type} (T : α → Trace) (L : Lang α) : Prop :=
  ∀ x, L x ↔ Halts (T x)

/-! ## 3. Polynomial Bounds -/

/--
`PolyBound f` means that `f` is bounded by a polynomial.
Formally: there exist constants `k` and `c` such that
  f n ≤ c * n^k + c
for all `n`.
-/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ (k c : ℕ), ∀ n : ℕ, f n ≤ c * (Nat.pow n k) + c

/-- The identity function is polynomially bounded. -/
lemma PolyBound_id : PolyBound id :=
  ⟨1, 1, fun n => by
    simp only [id]
    -- n ≤ 1 * n^1 + 1 = n + 1
    have h : 1 * Nat.pow n 1 + 1 = n + 1 := by simp [Nat.pow]
    rw [h]
    exact Nat.le_succ n⟩

/-- A constant function is polynomially bounded. -/
lemma PolyBound_const (c : ℕ) : PolyBound (fun _ => c) :=
  ⟨0, c, fun n => by
    -- Goal: c ≤ c * Nat.pow n 0 + c
    unfold Nat.pow
    simp only [Nat.mul_one]
    exact Nat.le_add_left c c⟩

/-! ## 4. Time-Bounded Decider for a Language -/

/--
`DecidableInTime T L size f` means:

* `T` decides exactly the language `L` (in the sense of `DecidesLang`).
* For each `x` in `L`, the trace `T x` halts in time ≤ `f (size x)`.

Note: For `x` not in `L`, `T x` never halts, so no bound is needed.
-/
structure DecidableInTime {α : Type}
    (T : α → Trace) (L : Lang α) (size : α → ℕ) (f : ℕ → ℕ) : Prop where
  decides    : DecidesLang T L
  time_bound : ∀ x, L x → HaltsInTime (T x) (f (size x))

/-! ## 5. Class P (RevHalt Version) -/

/--
`inP L size` means that the language `L` is decidable in polynomial time
by a family of traces, for the size function `size`.

Formally: there exist a trace family `T` and a polynomial bound `f`
such that `T` decides `L` in time `f`.
-/
def inP {α : Type} (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ (T : α → Trace) (f : ℕ → ℕ),
    PolyBound f ∧ DecidableInTime T L size f

/-! ## 6. Class NP (RevHalt Version) -/

/--
`inNP L size` means the language `L` is in NP for the size function `size`.

Formally, there exist:
* A certificate type `β` with size function `size_cert`.
* A relation `R : α → β → Prop`.
* A verification trace family `V : α → β → Trace`.
* A polynomial bound `g`.

Such that:
* `V` decides exactly `R` (as a language on pairs).
* The halting time on positive pairs `(x, y)` is bounded by `g (size x + size_cert y)`.
* `L x` iff there exists a certificate `y` such that `R x y`.
-/
def inNP {α : Type} (L : Lang α) (size : α → ℕ) : Prop :=
  ∃ (β : Type) (size_cert : β → ℕ)
    (R : α → β → Prop)
    (V : α → β → Trace)
    (g : ℕ → ℕ),
    PolyBound g ∧
    (∀ x y, R x y ↔ Halts (V x y)) ∧
    (∀ x y, R x y → HaltsInTime (V x y) (g (size x + size_cert y))) ∧
    (∀ x, L x ↔ ∃ y, R x y)

/-! ## 7. Basic Theorems -/

/-- P ⊆ NP: If L is in P, then L is in NP. -/
theorem P_subset_NP {α : Type} (L : Lang α) (size : α → ℕ) :
    inP L size → inNP L size := by
  intro ⟨T, f, hf_poly, hT_dec⟩
  -- Use Unit as certificate type (trivial certificates)
  refine ⟨Unit, fun _ => 0, fun x _ => L x, fun x _ => T x, f, hf_poly, ?_, ?_, ?_⟩
  · -- V decides R
    intro x _
    exact hT_dec.decides x
  · -- Time bound
    intro x _ hLx
    exact hT_dec.time_bound x hLx
  · -- L x ↔ ∃ y, R x y
    intro x
    constructor
    · intro hLx; exact ⟨(), hLx⟩
    · intro ⟨_, hRx⟩; exact hRx

/-- An always-true language is in P. -/
theorem true_lang_in_P (α : Type) (size : α → ℕ) :
    inP (fun _ : α => True) size := by
  refine ⟨fun _ => fun n => n = 0, fun _ => 0, ?_, ?_⟩
  · exact PolyBound_const 0
  · constructor
    · intro _
      constructor
      · intro _; exact ⟨0, rfl⟩
      · intro _; trivial
    · intro _ _
      exact ⟨0, Nat.le_refl 0, rfl⟩

/-- An always-false language is in P (vacuously). -/
theorem false_lang_in_P (α : Type) (size : α → ℕ) :
    inP (fun _ : α => False) size := by
  refine ⟨fun _ => fun _ => False, fun _ => 0, ?_, ?_⟩
  · exact PolyBound_const 0
  · constructor
    · intro _; simp [Halts]
    · intro _ h; exact h.elim

end RevComplexity
