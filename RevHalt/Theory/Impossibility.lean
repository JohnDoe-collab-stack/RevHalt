import RevHalt.Base
import RevHalt.Theory.Canonicity
import Mathlib.Computability.PartrecCode

/-!
# RevHalt.Theory.Impossibility

T2: Impossibility of Internalizing Rev associated with a Canonical Kit.

we use `Nat.Partrec.Code` + Kleene SRT (`fixed_point₂`)
to derive the diagonal bridge, and then refute any internal predicate that is
Total + Correct + Complete (and whose `Provable (Not (H e))` is r.e.).
-/

namespace RevHalt

open Nat.Partrec

/-- Concrete code model. -/
abbrev Code := Nat.Partrec.Code

/--
Machine trace: constant-in-time predicate “program terminates on input 0”.
-/
def Machine (c : Code) : Trace := fun _ => ∃ x : Nat, x ∈ c.eval 0

/-- `Halts (Machine c)` iff `c` converges on input `0`. -/
@[simp] lemma Halts_Machine_iff (c : Code) : Halts (Machine c) ↔ (∃ x : Nat, x ∈ c.eval 0) := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    exact hn
  · intro h
    exact ⟨0, h⟩

/--
Diagonal bridge (derived, no axioms):
from a semi-decider `f` for `target`, build `e` such that `Rev0_K K (Machine e) ↔ target e`.
-/
theorem diagonal_bridge
    (K : RHKit) (hK : DetectsMonotone K)
    (f : Code → (Nat →. Nat)) (hf : Partrec₂ f)
    (target : Code → Prop)
    (htarget : ∀ c, target c ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ e : Code, Rev0_K K (Machine e) ↔ target e := by
  rcases Nat.Partrec.Code.fixed_point₂ (f := f) hf with ⟨e, he⟩
  refine ⟨e, ?_⟩

  have hT1 : Rev0_K K (Machine e) ↔ Halts (Machine e) :=
    T1_traces K hK (Machine e)

  have hTerm : Halts (Machine e) ↔ (∃ x : Nat, x ∈ e.eval 0) :=
    Halts_Machine_iff e

  have hTarget : (∃ x : Nat, x ∈ e.eval 0) ↔ target e := by
    have : (∃ x : Nat, x ∈ e.eval 0) ↔ (∃ x : Nat, x ∈ (f e) 0) := by
      rw [he]
    exact (this.trans (htarget e).symm)

  exact hT1.trans (hTerm.trans hTarget)

/-- Minimal internal proof system data used by T2. -/
structure ImpossibleSystem (PropT : Type) where
  Provable : PropT → Prop
  FalseT   : PropT
  Not      : PropT → PropT
  consistent : ¬ Provable FalseT
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT

/--
Internalization attempt of `Rev0_K K (Machine e)` by a predicate `H e : PropT`,
with Total + Correct + Complete, plus r.e. semi-decidability of `Provable (Not (H e))`.
-/
structure InternalHaltingPredicate {PropT : Type}
    (S : ImpossibleSystem PropT) (K : RHKit) where
  H : Code → PropT
  total    : ∀ e, S.Provable (H e) ∨ S.Provable (S.Not (H e))
  correct  : ∀ e, Rev0_K K (Machine e) → S.Provable (H e)
  complete : ∀ e, ¬ Rev0_K K (Machine e) → S.Provable (S.Not (H e))
  f        : Code → (Nat →. Nat)
  f_partrec : Partrec₂ f
  semidec  : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)

/--
**T2** (packaged):
no such internalization predicate exists (axiom-free diagonalization).
-/
theorem T2_impossibility {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K) :
    ¬ ∃ _: InternalHaltingPredicate S K, True := by
  intro h
  rcases h with ⟨I, _⟩

  let target : Code → Prop := fun c => S.Provable (S.Not (I.H c))
  have diag := diagonal_bridge K hK I.f I.f_partrec target I.semidec
  rcases diag with ⟨e, he⟩
  -- he : Rev0_K K (Machine e) ↔ S.Provable (S.Not (I.H e))

  cases I.total e with
  | inl hProvH =>
      have hNotProvNotH : ¬ S.Provable (S.Not (I.H e)) :=
        fun hNot => S.consistent (S.absurd (I.H e) hProvH hNot)

      have hNotReal : ¬ Rev0_K K (Machine e) := mt he.mp hNotProvNotH
      have hProvNotH : S.Provable (S.Not (I.H e)) := I.complete e hNotReal
      exact hNotProvNotH hProvNotH

  | inr hProvNotH =>
      have hReal : Rev0_K K (Machine e) := he.mpr hProvNotH
      have hProvH : S.Provable (I.H e) := I.correct e hReal
      exact S.consistent (S.absurd (I.H e) hProvH hProvNotH)

end RevHalt
