import RevHalt.Base
import RevHalt.Theory.RECodePred
import Mathlib.Computability.PartrecCode

/-!

# RevHalt.Theory.Impossibility

T2: Impossibility of Internalizing Rev associated with a Canonical Kit.

**P1 Interpretation**:
This theorem also establishes the **Impossibility of Uniform Stabilization Detection**.
If we could uniformly decide which programs stabilize (P1), we could decide Halting (S1).
T2 ensures that the "Stabilization Certificates" extracted by T3 are **non-trivial** and **local**.

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
    (K : RHKit) (hK : DetectsUpFixed K)
    (f : Code → (Nat →. Nat)) (hf : Partrec₂ f)
    (target : Code → Prop)
    (htarget : ∀ c, target c ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ e : Code, Rev0_K K (Machine e) ↔ target e := by
  rcases Nat.Partrec.Code.fixed_point₂ (f := f) hf with ⟨e, he⟩
  refine ⟨e, ?_⟩

  have hT1 : Rev0_K K (Machine e) ↔ Halts (Machine e) := by
    simpa [Rev0_K] using (revK_iff_halts (K := K) hK (T := Machine e))

  have hTerm : Halts (Machine e) ↔ (∃ x : Nat, x ∈ e.eval 0) :=
    Halts_Machine_iff e

  have hTarget : (∃ x : Nat, x ∈ e.eval 0) ↔ target e := by
    have : (∃ x : Nat, x ∈ e.eval 0) ↔ (∃ x : Nat, x ∈ (f e) 0) := by
      rw [he]
    exact (this.trans (htarget e).symm)

  exact hT1.trans (hTerm.trans hTarget)

/-- `diagonal_bridge`, with the semi-decidability hypothesis bundled as an `RECodePred`. -/
theorem diagonal_bridge_re
    (K : RHKit) (hK : DetectsUpFixed K)
    (target : Code → Prop)
    (re : RECodePred target) :
    ∃ e : Code, Rev0_K K (Machine e) ↔ target e := by
  exact diagonal_bridge (K := K) (hK := hK) (f := re.f) (hf := re.f_partrec)
    (target := target) (htarget := re.spec)

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
no such internalization predicate exists (diagonalization / fixed point).

Audit note: the fixed-point machinery used here comes from `Mathlib.Computability.PartrecCode`,
and the axiom audit currently reports `Classical.choice` for this theorem.
-/
theorem T2_impossibility {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsUpFixed K) :
    ¬ ∃ _: InternalHaltingPredicate S K, True := by
  intro h
  rcases h with ⟨I, _⟩

  let target : Code → Prop := fun c => S.Provable (S.Not (I.H c))
  have diag :=
    diagonal_bridge_re (K := K) (hK := hK) (target := target)
      { f := I.f, f_partrec := I.f_partrec, spec := I.semidec }
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

/-- **T2 (DetectsMono API)**: No internalization of Rev0_K is possible. -/
theorem T2_impossibility_of_DetectsMono {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMono K) :
    ¬ ∃ _: InternalHaltingPredicate S K, True :=
  T2_impossibility S K ((DetectsMono_iff_DetectsUpFixed K).mp hK)

-- ==============================================================================================
-- Non-Fusion Invariance (Explicit Statement)
-- ==============================================================================================

/-!
## Non-Fusion Invariance Principle

The impossibility theorem T2 is **invariant under change of language/theory**.

Formally: for ANY choice of
- `PropT : Type` (the syntactic universe),
- `Provable : PropT → Prop` (the internal justification predicate),
- `Not : PropT → PropT` (internal negation),
- minimal coherence axioms (`consistent`, `absurd`),

the non-fusion result holds: there is no total, correct, complete internal predicate
that uniformly internalizes external certification (`Rev0_K`).

This invariance is captured by the universal quantification `{PropT : Type}` in T2_impossibility.
The result depends only on:
1. The Kit satisfying `DetectsUpFixed` (or equivalently `DetectsMono`)
2. The internal system satisfying minimal coherence
3. The semi-decidability of the negative case

It does NOT depend on:
- The specific language (PropT can be any type)
- The specific notion of provability
- Arithmetic, truth, or any particular domain

This makes T2 a **structural obstruction** to certification/justification fusion,
not a property of any particular formal system.
-/

/--
**Non-Fusion Invariance (Explicit)**:
For any type `PropT` and any `ImpossibleSystem` over it,
the fusion of external certification into internal justification is impossible.

This theorem is the explicit statement of language/theory invariance:
the result holds regardless of what `PropT`, `Provable`, `Not`, etc. are.
-/
theorem non_fusion_invariance
    (PropT : Type) (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsUpFixed K) :
    ¬ ∃ _ : InternalHaltingPredicate S K, True :=
  T2_impossibility S K hK

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Halts_Machine_iff
#print axioms RevHalt.diagonal_bridge
#print axioms RevHalt.diagonal_bridge_re
#print axioms RevHalt.T2_impossibility
#print axioms RevHalt.T2_impossibility_of_DetectsMono
#print axioms RevHalt.non_fusion_invariance
