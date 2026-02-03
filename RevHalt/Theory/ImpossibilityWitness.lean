import RevHalt.Theory.Impossibility

/-!
# RevHalt.Theory.ImpossibilityWitness

Witness-strengthening of the T2-style impossibility.

`no_uniform_internalizer_of_diagonal` proves `¬ Nonempty (Internalizer S Cert)`.
Here we extract the *witnessed obstruction* form:

For any attempted `Internalizer`, we can produce a specific code `e`
such that the internal system proves both `H e` and `Not (H e)`.

This matches the "obstruction" pattern used elsewhere in the project:
`forall global_procedure, exists local_counterexample`.
-/

namespace RevHalt

open Nat.Partrec

/--
Witnessed obstruction:
given a diagonal bridge for `Cert`, any purported `Internalizer` produces a specific `e`
where the internal system proves both sides.
-/
theorem inconsistent_witness_of_internalizer_of_diagonal {PropT : Type}
    (S : ImpossibleSystem PropT)
    (Cert : Code → Prop)
    (diag : DiagonalBridge Cert) :
    ∀ I : Internalizer S Cert,
      ∃ e : Code, S.Provable (I.H e) ∧ S.Provable (S.Not (I.H e)) := by
  intro I
  let target : Code → Prop := fun c => S.Provable (S.Not (I.H c))
  rcases diag target { f := I.f, f_partrec := I.f_partrec, spec := I.semidec } with ⟨e, he⟩
  cases I.total e with
  | inl hProvH =>
      -- from Provable(H e), consistency implies ¬ Provable(Not(H e))
      have hNotProvNotH : ¬ S.Provable (S.Not (I.H e)) :=
        fun hNot => S.consistent (S.absurd (I.H e) hProvH hNot)
      -- hence ¬ Cert e (since Cert e -> Provable(Not(H e)))
      have hNotCert : ¬ Cert e := mt he.mp hNotProvNotH
      -- but completeness forces Provable(Not(H e))
      have hProvNotH : S.Provable (S.Not (I.H e)) := I.complete e hNotCert
      exact ⟨e, hProvH, hProvNotH⟩
  | inr hProvNotH =>
      -- if Provable(Not(H e)), then Cert e, hence correctness gives Provable(H e)
      have hCert : Cert e := he.mpr hProvNotH
      have hProvH : S.Provable (I.H e) := I.correct e hCert
      exact ⟨e, hProvH, hProvNotH⟩

end RevHalt

-- Axiom checks (note: depends on whatever `diag` depends on):
#print axioms RevHalt.inconsistent_witness_of_internalizer_of_diagonal

