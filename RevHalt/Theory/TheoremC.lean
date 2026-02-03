import RevHalt.Theory.QuantifierSwap
import RevHalt.Theory.ImpossibilityWitness

/-!
# RevHalt.Theory.TheoremC

Packaged "Theorem C" (quantifier swap, complete form).

This file bundles:

1) Local repair / local extension (T3-style):
   for each instance `e`, there exists a sound local extension carrying a certificate sentence.

2) Global obstruction (T2-style, witnessed):
   for any attempted uniform internalizer, there exists a specific code `e`
   where the system proves both `H e` and `Not (H e)`.

This is the exact `forall global, exists counterexample` obstruction pattern.
-/

namespace RevHalt

open Nat.Partrec

theorem TheoremC_complete
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (M : PickCostModel S)
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    -- (1) Local extension exists for each instance `e`
    (∀ e, ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧ (∀ p ∈ S_e, Truth p) ∧ ((picks e).p ∈ S_e)) ∧
    -- (2) Witnessed global obstruction against any internalizer of the canonical machine predicate
    (∀ I : InternalHaltingPredicate S.toImpossibleSystem S.K,
      ∃ e : RevHalt.Code,
        S.Provable (I.H e) ∧ S.Provable (S.Not (I.H e))) := by
  constructor
  · -- local: already in QuantifierSwap theorem
    have h := (quantifier_swap_coexistence_quantified (S:=S) (Truth:=Truth) (S2:=S2)
      h_S2_sound (encode_halt:=encode_halt) (encode_not_halt:=encode_not_halt)
      h_pos h_neg (M:=M) (picks:=picks))
    exact h.2.1
  · -- obstruction: use diagonal bridge for Rev + witness strengthening
    intro I
    -- diagonal bridge for the certification predicate `Rev0_K S.K (Machine _)`
    have diag : DiagonalBridge (fun e : RevHalt.Code => Rev0_K S.K (RevHalt.Machine e)) :=
      diagonalBridge_for_Rev S.K S.h_canon
    -- apply witnessed obstruction lemma
    simpa [InternalHaltingPredicate] using
      (inconsistent_witness_of_internalizer_of_diagonal (S:=S.toImpossibleSystem)
        (Cert := fun e : RevHalt.Code => Rev0_K S.K (RevHalt.Machine e))
        diag I)

end RevHalt

-- Axiom checks (inherits the fixed-point axioms via `diagonalBridge_for_Rev`):
#print axioms RevHalt.TheoremC_complete

