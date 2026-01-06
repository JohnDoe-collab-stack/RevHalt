import RevHalt.Base
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Impossibility
import RevHalt.Theory.Stabilization
import RevHalt.Theory.Categorical
import RevHalt.Theory.Arithmetization.HaltsSigma1

/-!
# RevHalt.Theory.KernelUndecidability

This file proves that the kernel of `up` (= Stabilizes = ¬Halts) is **not semi-decidable**.

## Main Theorem

`stabilizes_not_re`: There is no `RECodePred` for the predicate `fun e => ¬ Rev0_K K (Machine e)`.

This is a direct consequence of T2 (Impossibility): if we could semi-decide stabilization,
together with the existing semi-decidability of halting (`reHaltsSigma1`), we would have
a complete decidable predicate, which contradicts T2.

## Corollary

Since `upKernel = { T | Stabilizes T }` and the restriction to `Machine` traces is not r.e.,
the kernel itself is not "uniformly semi-decidable" in the computational sense.
-/

namespace RevHalt

open Nat.Partrec

/-!
## The Core Theorem
-/

/--
**Stabilization is not semi-decidable (r.e.)**.

If it were, we could build an `InternalHaltingPredicate` and contradict T2.

The proof works as follows:
1. We already have `reHaltsSigma1 : RECodePred HaltsSigma1` (halting is r.e.).
2. Suppose we also had `RECodePred (fun e => ¬ Rev0_K K (Machine e))` (stabilization is r.e.).
3. We can build an `InternalHaltingPredicate` with:
   - `H e` = "e halts" as a syntactic object
   - `Provable (H e)` = witness of halting
   - `Provable (Not (H e))` = witness of stabilization
4. This predicate would be Total + Correct + Complete + semidec.
5. T2 says no such predicate exists.
6. Contradiction.
-/
theorem stabilizes_not_re (K : RHKit) (hK : DetectsMonotone K) :
    RECodePred (fun e : Code => ¬ Rev0_K K (Machine e)) → False := by
  intro hRE
  -- Build a trivial proof system where Provable = Truth.
  let S : ImpossibleSystem Prop := {
    Provable := fun p => p
    FalseT := False
    Not := fun p => ¬ p
    consistent := fun h => h
    absurd := fun _ hp hnp => hnp hp
  }
  -- Build the InternalHaltingPredicate
  let I : InternalHaltingPredicate S K := {
    H := fun e => Rev0_K K (Machine e)
    total := fun e => Classical.em (Rev0_K K (Machine e))
    correct := fun e h => h
    complete := fun e h => h
    f := hRE.f
    f_partrec := hRE.f_partrec
    semidec := fun c => hRE.spec c
  }
  -- Apply T2
  exact T2_impossibility S K hK ⟨I, trivial⟩

/--
Corollary: The kernel of `up` is not semi-decidable when restricted to Machine traces.

This is just a rephrasing using `Stabilizes` instead of `¬ Rev0_K`.
-/
theorem kernel_not_re (K : RHKit) (hK : DetectsMonotone K) :
    RECodePred (fun e : Code => Stabilizes (Machine e)) → False := by
  intro hRE
  exact stabilizes_not_re K hK {
    f := hRE.f
    f_partrec := hRE.f_partrec
    -- Need: ¬ Rev0_K K (Machine e) ↔ (∃ x, x ∈ hRE.f e 0)
    -- KitStabilizes K T = ¬ Rev0_K K T (definitional)
    -- T1_stabilization: KitStabilizes K T ↔ Stabilizes T
    -- hRE.spec e: Stabilizes (Machine e) ↔ (∃ x, x ∈ hRE.f e 0)
    -- Chain: KitStabilizes ↔ Stabilizes ↔ (∃ x, ...)
    spec := fun e => (T1_stabilization K hK (Machine e)).trans (hRE.spec e)
  }

/--
**Halting/Stabilization are computationally separated:**
Halting is Σ₁ (semi-decidable), but Stabilization is not.

This is the computational content of the Halt/Gödel barrier.
-/
theorem halts_sigma1_stabilizes_not_sigma1 (K : RHKit) (hK : DetectsMonotone K) :
    Nonempty (RECodePred fun e : Code => Rev0_K K (Machine e)) ∧
    (RECodePred (fun e : Code => ¬ Rev0_K K (Machine e)) → False) := by
  constructor
  · -- Halting is r.e.
    exact ⟨Arithmetic.reRev0KMachine K hK⟩
  · -- Stabilization is not r.e.
    exact stabilizes_not_re K hK

end RevHalt

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.stabilizes_not_re
#print axioms RevHalt.kernel_not_re
#print axioms RevHalt.halts_sigma1_stabilizes_not_sigma1
