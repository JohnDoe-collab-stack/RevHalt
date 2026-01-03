import RevHalt.Theory.Impossibility
import RevHalt.Theory.RECodePred

/-!
# RevHalt.Theory.GodelLens

This file makes the “Gödel direction” explicit **as a lens**: it repackages `T2_impossibility` into
statements that look like incompleteness, without yet committing to a concrete arithmetization.

The core message is interface-based (RevHalt style):

- If a system can internally *totalize* a predicate `H` that is both correct and complete for `Rev0_K`,
  and if refutability `Provable (Not (H e))` is r.e. (has a semi-decider), then contradiction follows.

We keep the main statement constructive *in shape* (no witness extraction), and isolate any “there exists an
undecidable sentence” corollary behind an explicit `classical` block.

Audit note: the underlying fixed-point machinery comes from `Mathlib.Computability.PartrecCode`, and the
axiom audit currently reports `Classical.choice` for `T2_impossibility`; this file inherits that dependency.
-/

namespace RevHalt

open Nat.Partrec

section

variable {PropT : Type}

/-- “Decides every code”: the internal system proves either `H e` or `¬H e` for all `e`. -/
def Decides (S : ImpossibleSystem PropT) (H : Code → PropT) : Prop :=
  ∀ e, S.Provable (H e) ∨ S.Provable (S.Not (H e))

/-!
## Gödel I (standard shape): a true but unprovable sentence

The following is the minimal “Gödel I” output RevHalt can already deliver, without committing to a
concrete arithmetization:

If a system is consistent and can (i) prove the positive halting predicate `H e` whenever halting is
semantically true, and (ii) semi-decide refutability `Provable (¬H e)`, then there exists a code `e`
that does not halt, yet whose non-halting statement `¬H e` is not provable.

With an external semantics `Truth` that interprets `H` as halting, this yields a sentence that is
true but not provable (Gödel-I style).
-/

/--
Gödel-I (constructive): there exists an `e` such that `e` does not halt, yet `¬H e` is not provable.

This uses only:
- consistency of `S` (already inside `ImpossibleSystem`),
- positive correctness (`Rev0_K … → Provable (H e)`),
- r.e. refutability of `H` (a semi-decider for `Provable (¬H e)`),
and the diagonal bridge (`fixed_point₂`).
-/
theorem exists_nonhalting_unprovable_neg_of_correct_semidec
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (f : Code → (Nat →. Nat))
    (f_partrec : Partrec₂ f)
    (semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ e, ¬ Rev0_K K (Machine e) ∧ ¬ S.Provable (S.Not (H e)) := by
  -- Diagonalize against refutability: `Rev0_K … ↔ Provable (¬H e)`.
  have diag :=
    diagonal_bridge (K := K) (hK := hK)
      (f := f) f_partrec
      (target := fun c => S.Provable (S.Not (H c)))
      (htarget := semidec)
  rcases diag with ⟨e, he⟩

  have hNotProvNot : ¬ S.Provable (S.Not (H e)) := by
    intro hProvNot
    have hReal : Rev0_K K (Machine e) := he.mpr hProvNot
    have hProvH : S.Provable (H e) := correct e hReal
    exact S.consistent (S.absurd (H e) hProvH hProvNot)

  have hNotReal : ¬ Rev0_K K (Machine e) := mt he.mp hNotProvNot
  exact ⟨e, hNotReal, hNotProvNot⟩

/-- Same as `exists_nonhalting_unprovable_neg_of_correct_semidec`, but with the r.e. hypothesis bundled. -/
theorem exists_nonhalting_unprovable_neg_of_correct_re
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (re : RECodePred fun c => S.Provable (S.Not (H c))) :
    ∃ e, ¬ Rev0_K K (Machine e) ∧ ¬ S.Provable (S.Not (H e)) := by
  exact
    exists_nonhalting_unprovable_neg_of_correct_semidec
      (S := S) (K := K) (hK := hK)
      (H := H) (correct := correct)
      (f := re.f) (f_partrec := re.f_partrec) (semidec := re.spec)

/--
Gödel-I (semantic form): assuming an external truth predicate interpreting `H` as halting,
there exists a sentence that is true but not provable.
-/
theorem godelI_exists_true_unprovable_of_correct_semidec
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (Truth : PropT → Prop)
    (truth_not : ∀ p, Truth (S.Not p) ↔ ¬ Truth p)
    (H : Code → PropT)
    (truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e))
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (f : Code → (Nat →. Nat))
    (f_partrec : Partrec₂ f)
    (semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ p, Truth p ∧ ¬ S.Provable p := by
  rcases
      exists_nonhalting_unprovable_neg_of_correct_semidec
        (S := S) (K := K) (hK := hK)
        (H := H) (correct := correct)
        (f := f) (f_partrec := f_partrec) (semidec := semidec)
    with ⟨e, hNotReal, hNotProv⟩

  have hNotTruthH : ¬ Truth (H e) := by
    intro hTH
    have : Rev0_K K (Machine e) := (truth_H e).1 hTH
    exact hNotReal this

  have hTruthNotH : Truth (S.Not (H e)) := (truth_not (H e)).2 hNotTruthH
  exact ⟨S.Not (H e), hTruthNotH, hNotProv⟩

/-- Same as `godelI_exists_true_unprovable_of_correct_semidec`, but with the r.e. hypothesis bundled. -/
theorem godelI_exists_true_unprovable_of_correct_re
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (Truth : PropT → Prop)
    (truth_not : ∀ p, Truth (S.Not p) ↔ ¬ Truth p)
    (H : Code → PropT)
    (truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e))
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (re : RECodePred fun c => S.Provable (S.Not (H c))) :
    ∃ p, Truth p ∧ ¬ S.Provable p := by
  exact
    godelI_exists_true_unprovable_of_correct_semidec
      (S := S) (K := K) (hK := hK)
      (Truth := Truth) (truth_not := truth_not)
      (H := H) (truth_H := truth_H) (correct := correct)
      (f := re.f) (f_partrec := re.f_partrec) (semidec := re.spec)

/--
Gödel lens (no witness extraction):
under correctness + completeness + r.e. refutability, totality is impossible.

This is constructive in the sense that it produces a refutation of totality without selecting a specific
counterexample `e`.
-/
theorem not_total_of_correct_complete_semidec
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (complete : ∀ e, ¬ Rev0_K K (Machine e) → S.Provable (S.Not (H e)))
    (f : Code → (Nat →. Nat))
    (f_partrec : Partrec₂ f)
    (semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ¬ Decides (S := S) H := by
  intro hTotal
  have : ∃ _ : InternalHaltingPredicate S K, True := by
    refine ⟨{ H := H
            , total := hTotal
            , correct := correct
            , complete := complete
            , f := f
            , f_partrec := f_partrec
            , semidec := semidec }, trivial⟩
  exact (T2_impossibility (S := S) (K := K) hK) this

/-- Same as `not_total_of_correct_complete_semidec`, but with the r.e. hypothesis bundled. -/
theorem not_total_of_correct_complete_re
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (complete : ∀ e, ¬ Rev0_K K (Machine e) → S.Provable (S.Not (H e)))
    (re : RECodePred fun c => S.Provable (S.Not (H c))) :
    ¬ Decides (S := S) H := by
  exact
    not_total_of_correct_complete_semidec
      (S := S) (K := K) (hK := hK)
      (H := H) (correct := correct) (complete := complete)
      (f := re.f) (f_partrec := re.f_partrec) (semidec := re.spec)

/--
Classical witness extraction:
if totality is impossible, then there exists a specific `e` such that neither `H e` nor `¬H e` is provable.

This is the closest “Gödel-I shape” we can state without arithmetizing `PropT`.
-/
theorem exists_undecidable_classical_of_correct_complete_semidec
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (complete : ∀ e, ¬ Rev0_K K (Machine e) → S.Provable (S.Not (H e)))
    (f : Code → (Nat →. Nat))
    (f_partrec : Partrec₂ f)
    (semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ e, ¬ S.Provable (H e) ∧ ¬ S.Provable (S.Not (H e)) := by
  classical
  have hNotTotal :
      ¬ Decides (S := S) H :=
    not_total_of_correct_complete_semidec
      (S := S) (K := K) (hK := hK)
      (H := H) (correct := correct) (complete := complete)
      (f := f) (f_partrec := f_partrec) (semidec := semidec)

  have hExists :
      ∃ e, ¬ (S.Provable (H e) ∨ S.Provable (S.Not (H e))) := by
    by_contra hNone
    have hDouble : ∀ e, ¬¬ (S.Provable (H e) ∨ S.Provable (S.Not (H e))) := by
      intro e hNeg
      exact hNone ⟨e, hNeg⟩
    have hAll : Decides (S := S) H := by
      intro e
      exact Classical.not_not.mp (hDouble e)
    exact hNotTotal hAll

  rcases hExists with ⟨e, hNo⟩
  refine ⟨e, ?_, ?_⟩
  · intro hProv
    exact hNo (Or.inl hProv)
  · intro hProvNot
    exact hNo (Or.inr hProvNot)

/--
Classical “true but unprovable” corollary, given an external truth predicate.

This is the classical Gödel-I shape: there exists a sentence that is true (in the external semantics)
but not provable by the internal system.

Assumptions:
- `Truth : PropT → Prop` is an external semantics.
- `truth_not` says `S.Not` matches semantic negation.
- We use the previous lemma to obtain an undecidable `e`, and then pick the true side.
-/
theorem exists_true_unprovable_classical_of_correct_complete_semidec
    (S : ImpossibleSystem PropT)
    (K : RHKit) (hK : DetectsMonotone K)
    (Truth : PropT → Prop)
    (truth_not : ∀ p, Truth (S.Not p) ↔ ¬ Truth p)
    (H : Code → PropT)
    (correct : ∀ e, Rev0_K K (Machine e) → S.Provable (H e))
    (complete : ∀ e, ¬ Rev0_K K (Machine e) → S.Provable (S.Not (H e)))
    (f : Code → (Nat →. Nat))
    (f_partrec : Partrec₂ f)
    (semidec : ∀ c, S.Provable (S.Not (H c)) ↔ (∃ x : Nat, x ∈ (f c) 0)) :
    ∃ p, Truth p ∧ ¬ S.Provable p := by
  classical
  rcases
      exists_undecidable_classical_of_correct_complete_semidec
        (S := S) (K := K) (hK := hK)
        (H := H) (correct := correct) (complete := complete)
        (f := f) (f_partrec := f_partrec) (semidec := semidec)
    with ⟨e, hNotH, hNotNotH⟩

  by_cases hT : Truth (H e)
  · exact ⟨H e, hT, hNotH⟩
  · have hTNot : Truth (S.Not (H e)) := (truth_not (H e)).2 hT
    exact ⟨S.Not (H e), hTNot, hNotNotH⟩

end

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.not_total_of_correct_complete_semidec
#print axioms RevHalt.not_total_of_correct_complete_re
#print axioms RevHalt.exists_undecidable_classical_of_correct_complete_semidec
#print axioms RevHalt.exists_true_unprovable_classical_of_correct_complete_semidec
#print axioms RevHalt.exists_nonhalting_unprovable_neg_of_correct_semidec
#print axioms RevHalt.exists_nonhalting_unprovable_neg_of_correct_re
#print axioms RevHalt.godelI_exists_true_unprovable_of_correct_semidec
#print axioms RevHalt.godelI_exists_true_unprovable_of_correct_re
