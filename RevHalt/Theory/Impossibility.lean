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

-- ==============================================================================================
-- Abstract Diagonal Bridge (Cert-parameterized)
-- ==============================================================================================

/--
**DiagonalBridge**: A certification predicate `Cert : Code → Prop` admits a diagonal bridge
if for any r.e. target, there exists a code whose certification status equals the target.

This is the abstract property that enables the non-fusion argument.
Any predicate with this property cannot be uniformly internalized.
-/
def DiagonalBridge (Cert : Code → Prop) : Prop :=
  ∀ target : Code → Prop, RECodePred target → ∃ e, Cert e ↔ target e

/--
**Rev0_K admits diagonal bridge**: The concrete certification predicate `Rev0_K K (Machine _)`
satisfies the DiagonalBridge property (via Kleene fixed point).
-/
theorem diagonalBridge_for_Rev
    (K : RHKit) (hK : DetectsUpFixed K) :
    DiagonalBridge (fun e => Rev0_K K (Machine e)) := by
  intro target re
  exact diagonal_bridge_re (K := K) (hK := hK) (target := target) re

/-- Minimal internal proof system data used by T2. -/
structure ImpossibleSystem (PropT : Type) where
  Provable : PropT → Prop
  FalseT   : PropT
  Not      : PropT → PropT
  consistent : ¬ Provable FalseT
  absurd     : ∀ p, Provable p → Provable (Not p) → Provable FalseT

/--
**Internalizer**: Abstract internalization attempt of ANY external certification `Cert : Code → Prop`.

This is the fully general version: the external predicate is a parameter, not hardcoded to Rev0_K.
The non-fusion invariant holds for ANY Cert that admits a DiagonalBridge.
-/
structure Internalizer {PropT : Type}
    (S : ImpossibleSystem PropT) (Cert : Code → Prop) where
  H : Code → PropT
  total    : ∀ e, S.Provable (H e) ∨ S.Provable (S.Not (H e))
  correct  : ∀ e, Cert e → S.Provable (H e)
  complete : ∀ e, ¬ Cert e → S.Provable (S.Not (H e))
  f        : Code → (Nat →. Nat)
  f_partrec : Partrec₂ f
  semidec  : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)

/--
**InternalHaltingPredicate**: Specialized Internalizer for Rev0_K (legacy API).
-/
abbrev InternalHaltingPredicate {PropT : Type}
    (S : ImpossibleSystem PropT) (K : RHKit) :=
  Internalizer S (fun e => Rev0_K K (Machine e))

/--
**General Non-Fusion Theorem**: For ANY external certification `Cert` that admits a DiagonalBridge,
no uniform Internalizer (Total + Correct + Complete + r.e. negative) exists.

This is the fully abstract form of the non-fusion invariant:
- Parameterized by `PropT` (language independence)
- Parameterized by `Cert` (external phenomenon independence)
- Depends only on minimal coherence interface and DiagonalBridge

The invariant: diagonal bridge + coherent internal system + r.e. negative ⇒ no uniform fusion.
-/
theorem no_uniform_internalizer_of_diagonal {PropT : Type}
    (S : ImpossibleSystem PropT)
    (Cert : Code → Prop)
    (diag : DiagonalBridge Cert) :
    ¬ Nonempty (Internalizer S Cert) := by
  intro ⟨I⟩

  let target : Code → Prop := fun c => S.Provable (S.Not (I.H c))
  have diag_app :=
    diag target { f := I.f, f_partrec := I.f_partrec, spec := I.semidec }
  rcases diag_app with ⟨e, he⟩
  -- he : Cert e ↔ S.Provable (S.Not (I.H e))

  cases I.total e with
  | inl hProvH =>
      have hNotProvNotH : ¬ S.Provable (S.Not (I.H e)) :=
        fun hNot => S.consistent (S.absurd (I.H e) hProvH hNot)
      have hNotCert : ¬ Cert e := mt he.mp hNotProvNotH
      have hProvNotH : S.Provable (S.Not (I.H e)) := I.complete e hNotCert
      exact hNotProvNotH hProvNotH

  | inr hProvNotH =>
      have hCert : Cert e := he.mpr hProvNotH
      have hProvH : S.Provable (I.H e) := I.correct e hCert
      exact S.consistent (S.absurd (I.H e) hProvH hProvNotH)

/--
**T2** (packaged):
no such internalization predicate exists (diagonalization / fixed point).

Audit note: the fixed-point machinery used here comes from `Mathlib.Computability.PartrecCode`,
and the axiom audit currently reports `Classical.choice` for this theorem.
-/
theorem T2_impossibility {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsUpFixed K) :
    ¬ Nonempty (InternalHaltingPredicate S K) := by
  intro ⟨I⟩

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
    ¬ Nonempty (InternalHaltingPredicate S K) :=
  T2_impossibility S K ((DetectsMono_iff_DetectsUpFixed K).mp hK)

-- ==============================================================================================
-- Non-Fusion Invariance (Explicit Statement)
-- ==============================================================================================

/-!
## Non-Fusion Invariance Principle

The impossibility theorem is **invariant under change of language/theory AND external phenomenon**.

### Language/Theory Independence (PropT)

For ANY choice of
- `PropT : Type` (the syntactic universe),
- `Provable : PropT → Prop` (the internal justification predicate),
- `Not : PropT → PropT` (internal negation),
- minimal coherence axioms (`consistent`, `absurd`),

the non-fusion result holds.

It does NOT depend on any specific proof calculus beyond the minimal coherence interface.

### External Phenomenon Independence (Cert)

For ANY external certification predicate `Cert : Code → Prop` that admits a **DiagonalBridge**
(i.e., for any r.e. target there exists a code whose certification equals the target),
no uniform Internalizer exists.

`Rev0_K K (Machine _)` is just one instance of such a Cert (via `diagonalBridge_for_Rev`).

### The Invariant (Formal)

```
∀ PropT Cert S, DiagonalBridge Cert → ¬ ∃ I : Internalizer S Cert, True
```

This is a **structural obstruction** to certification/justification fusion,
not a property of any particular formal system or external phenomenon.
-/

/--
**Non-Fusion Invariance (Full)**: For any Cert with DiagonalBridge, fusion is impossible.
This is the fully abstract form of the non-fusion principle.
-/
theorem non_fusion_invariance_full
    (PropT : Type) (S : ImpossibleSystem PropT)
    (Cert : Code → Prop) (diag : DiagonalBridge Cert) :
    ¬ Nonempty (Internalizer S Cert) :=
  no_uniform_internalizer_of_diagonal S Cert diag

/--
**T2 as Corollary**: The original T2 (Rev0_K specific) follows from the general theorem.
-/
theorem T2_from_general {PropT : Type}
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsUpFixed K) :
    ¬ Nonempty (Internalizer S (fun e => Rev0_K K (Machine e))) :=
  no_uniform_internalizer_of_diagonal S _ (diagonalBridge_for_Rev K hK)

/--
**Non-Fusion Invariance (Legacy API)**: For Rev0_K specifically, fusion is impossible.
(Redirects to T2_impossibility for compatibility.)
-/
theorem non_fusion_invariance
    (PropT : Type) (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsUpFixed K) :
    ¬ Nonempty (InternalHaltingPredicate S K) :=
  T2_impossibility S K hK

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.Halts_Machine_iff
#print axioms RevHalt.diagonal_bridge
#print axioms RevHalt.diagonal_bridge_re
#print axioms RevHalt.DiagonalBridge
#print axioms RevHalt.diagonalBridge_for_Rev
#print axioms RevHalt.Internalizer
#print axioms RevHalt.no_uniform_internalizer_of_diagonal
#print axioms RevHalt.T2_impossibility
#print axioms RevHalt.T2_impossibility_of_DetectsMono
#print axioms RevHalt.non_fusion_invariance_full
#print axioms RevHalt.T2_from_general
#print axioms RevHalt.non_fusion_invariance
