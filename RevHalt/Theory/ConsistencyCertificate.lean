-- RevHalt/Theory/ConsistencyCertificate.lean
import RevHalt.Theory.Complementarity
import RevHalt.Theory.Canonicity
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.ConsistencyCertificate

A minimal, ordinal-free "consistency-style" move in the RevHalt framework:

Given a system `S : ComplementaritySystem Code PropT`, a base corpus `S2 : Set PropT`
(sound w.r.t. an external predicate `Truth`), and a code `e` such that the *canonical
verdict* says `¬ Rev0_K S.K (S.Machine e)` (equivalently `¬ Halts (S.Machine e)` by T1),
we can soundly extend `S2` by adding the single sentence `encode_not_halt e`.

This is the local, two-sided "negative certificate" step, with no ordinals and no
model-theoretic machinery inside the proof: everything is expressed via `Rev0_K` + T1.
-/

namespace RevHalt

theorem extend_S2_with_negative_certificate
    {Code PropT : Type}
    (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_not_halt : Code → PropT)
    (h_encode_neg : ∀ e, ¬ Rev0_K S.K (S.Machine e) → Truth (encode_not_halt e))
    (e : Code)
    (hNotRev : ¬ Rev0_K S.K (S.Machine e))
    (hUnprov : ¬ S.Provable (encode_not_halt e)) :
    ∃ S3 : Set PropT,
      S3 = S2 ∪ ({encode_not_halt e} : Set PropT) ∧
      S2 ⊆ S3 ∧
      (∀ p ∈ S3, Truth p) ∧
      encode_not_halt e ∈ S3 ∧
      ¬ S.Provable (encode_not_halt e) ∧
      ¬ Halts (S.Machine e) := by
  let S3 : Set PropT := S2 ∪ ({encode_not_halt e} : Set PropT)

  have hIff : Rev0_K S.K (S.Machine e) ↔ Halts (S.Machine e) :=
    T1_traces S.K S.h_canon (S.Machine e)

  have hNotHalt : ¬ Halts (S.Machine e) := by
    intro hHalt
    exact hNotRev (hIff.2 hHalt)

  have hTruthNew : Truth (encode_not_halt e) :=
    h_encode_neg e hNotRev

  refine ⟨S3, rfl, ?_, ?_, ?_, hUnprov, hNotHalt⟩

  · -- S2 ⊆ S3
    intro p hp
    exact Or.inl hp

  · -- soundness of S3
    intro p hp
    cases hp with
    | inl hp2 =>
        exact h_S2_sound p hp2
    | inr hp1 =>
        -- hp1 : p ∈ {encode_not_halt e}  i.e. p = encode_not_halt e
        have hpEq : p = encode_not_halt e := hp1
        rw [hpEq]
        exact hTruthNew

  · -- encode_not_halt e ∈ S3
    have hMemSingleton : encode_not_halt e ∈ ({encode_not_halt e} : Set PropT) := rfl
    exact Or.inr hMemSingleton

end RevHalt
