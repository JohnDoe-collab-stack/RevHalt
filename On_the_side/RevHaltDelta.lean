import RevHalt
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-!
# RevHaltDelta: Finite Halting Counters and Delta Invariant

This module adds, on top of the `RevHalt` framework, a small
quantitative invariant on traces:

* `countTrue N T` : number of steps `0 ≤ k < N` where the trace `T` is `true`
* `allTrue N T`   : all steps `0 ≤ k < N` are `true`
* `deltaScaled N T` : a finite "score" derived from the trace

and two basic lemmas:

* `DR0` : `deltaScaled N T = 0 ↔ allTrue N T`
* `DR1` : if `¬ allTrue N T` then `deltaScaled N T ≥ N`

This is the abstract version of the original DR0/DR1 results
formulated on `Program` and `haltsWithinBool`, but here directly
on the `Trace` from the RevHalt framework.
-/

namespace RevHaltDelta

open Nat List

/-! ## 1. Finite counters on traces -/

/--
`countTrue N T` : number of instants `k` with `0 ≤ k < N` where `T k` is true.
We use `List.range N = [0, 1, ..., N-1]` and `countP` with decidable predicate.
-/
def countTrue (N : ℕ) (T : Trace) [DecidablePred T] : ℕ :=
  (range N).countP (fun n => T n)

/--
`allTrue N T` : all instants `k < N` are true in the trace `T`.
-/
def allTrue (N : ℕ) (T : Trace) : Prop :=
  ∀ k < N, T k

/-- List-based version: equivalence between `allTrue` and a property on `range N`. -/
lemma allTrue_iff_range (N : ℕ) (T : Trace) :
    allTrue N T ↔ ∀ k ∈ range N, T k := by
  simp [allTrue, mem_range]

/-- `allTrue` is decidable when we have a decidable predicate. -/
instance allTrue_decidable (N : ℕ) (T : Trace) [DecidablePred T] : Decidable (allTrue N T) :=
  decidable_of_iff (∀ k ∈ range N, T k) (allTrue_iff_range N T).symm

/-! ## 2. Delta scalar on a finite window -/

/--
`deltaScaled N T` : quantitative invariant derived from the trace `T` on the window `[0, N)`.

* If all instants `k < N` are true (`allTrue N T`), we set `0`.
* Otherwise, we set `N + countTrue N T`.

This scheme reflects exactly the original Java/Lean definition on programs,
but generalized to any trace.
-/
def deltaScaled (N : ℕ) (T : Trace) [DecidablePred T] : ℕ :=
  if allTrue N T then 0 else N + countTrue N T

/-! ## 3. DR0 : delta = 0 ↔ all steps are true -/

/--
**DR0 (Delta-Result 0)** :
`deltaScaled N T = 0` if and only if the trace is true everywhere on `[0, N)`.

This is the abstraction of the fact that, in the VM, `delta = 0` characterizes
the case "everything halted" on the window.
-/
theorem DR0 (N : ℕ) (T : Trace) [DecidablePred T] :
    deltaScaled N T = 0 ↔ allTrue N T := by
  unfold deltaScaled
  constructor
  · -- (→) if delta = 0 then allTrue
    intro hδ
    by_contra hNotAll
    -- Under ¬allTrue, we are in the branch N + countTrue
    have hsum : N + countTrue N T = 0 := by
      simpa [hNotAll] using hδ
    -- On ℕ, a + b = 0 ⇒ a = 0 ∧ b = 0
    have hzero : N = 0 ∧ countTrue N T = 0 :=
      Nat.add_eq_zero_iff.mp hsum
    have hN0 : N = 0 := hzero.1
    subst hN0
    -- But allTrue 0 T is trivially true, contradiction
    have : allTrue 0 T := by simp [allTrue]
    exact hNotAll this
  · -- (←) if allTrue then delta = 0
    intro hAll
    simp [hAll]

/-! ## 4. DR1 : if not all true, then delta ≥ N -/

/--
**DR1 (Delta-Result 1)** :
If all instants `k < N` are **not** true (`¬ allTrue N T`),
then `deltaScaled N T ≥ N`.

Intuition: as soon as there is a "defect" in the window,
we are in the branch `N + countTrue`, so always ≥ N.
-/
theorem DR1 (N : ℕ) (T : Trace) [DecidablePred T] (h : ¬ allTrue N T) :
    deltaScaled N T ≥ N := by
  unfold deltaScaled
  simp only [h, ↓reduceIte]
  exact Nat.le_add_right N (countTrue N T)

/-! ## 5. Trivial monotonicity for monotone traces -/

/--
For reference: if the trace is monotone in the sense of `Monotone T`,
then as soon as we have `T n` and `n ≤ m`, we have `T m`.

This is immediate from the definition of `Monotone`, but we isolate it
because it was the substance of `haltsWithinBool_mono` in the original code.
-/
lemma trace_mono_forward (T : Trace) (hMono : Monotone T)
    {n m : ℕ} (h_le : n ≤ m) (hn : T n) :
    T m :=
  hMono h_le hn

end RevHaltDelta
