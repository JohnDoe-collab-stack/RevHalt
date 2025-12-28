/-
  RevHalt.Examples.TwoSidedFrontier

  Demonstrates the two-sided complementarity mechanism:
  1. oraclePick_to_edge: binary (always valid) — OraclePick → Edge
  2. oraclePick_to_fork_step: complementary (requires hcomp) — OraclePick → Fork-step

  Key point: no `Decidable`, no global chooser. Certificate carries the branch.
-/

import RevHalt.Bridge.Context
import RevHalt.Theory.Complementarity
import RevHalt.Dynamics.Core.Node
import RevHalt.Dynamics.Core.Move
import RevHalt.Dynamics.Core.Graph
import RevHalt.Dynamics.Core.Fork

namespace RevHalt.Examples

open RevHalt.Dynamics.Core
open Set

variable {Code PropT : Type}

/-!
## Lemma 1: Binary bifurcation (always valid)

OraclePick produces an Edge without requiring complementarity.
This formalizes: "certificate → local extension" without exclusion.
-/

/-- Binary bifurcation: OraclePick → Edge (always valid, no Fork).

This lemma shows that a certificate (OraclePick) produces a local extension.
No complementarity is required. No exclusion is provided.
This is the "binary" two-sided, not the "Fork" two-sided.
-/
theorem oraclePick_to_edge
    (ctx : EnrichedContext Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code)
    (T0 : TheoryNode ctx)
    (hpos : Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_halt e))
    (hneg : ¬ Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_not_halt e))
    (pick : OraclePick (S := ctx.toComplementaritySystem)
              encode_halt encode_not_halt e) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ pick.p ∈ T1.theory := by
  classical

  -- 1) Extract Truth(pick.p) from the certificate
  have hp : ctx.Truth pick.p := by
    rcases pick.cert with ⟨hR, hpEq⟩ | ⟨hNR, hpEq⟩
    · -- positive branch: p = encode_halt e
      rw [hpEq]
      exact hpos hR
    · -- negative branch: p = encode_not_halt e
      rw [hpEq]
      exact hneg hNR

  -- 2) Build the extension via Move.extend
  let m : Move ctx := Move.extend pick.p hp
  let T1 : TheoryNode ctx := Move.apply m T0

  refine ⟨T1, Edge.of_move m T0, ?_⟩

  -- 3) Membership: pick.p ∈ Extend T0.theory pick.p
  simp only [T1, m, Move.apply_extend_theory, mem_Extend_iff]
  right
  trivial

/-!
## Lemma 2: Complementary bifurcation (Fork)

OraclePick → Fork-step, but ONLY if the negative branch is `Not` of the positive.
This gives Fork's exclusion property.
-/

/-- Complementary bifurcation: OraclePick → Fork-step.

Requires: `encode_not_halt e = ctx.Not (encode_halt e)` (complementarity).
This lemma uses Fork.ofPivot and gets exclusion for free.
-/
theorem oraclePick_to_fork_step
    (ctx : EnrichedContext Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code)
    (T0 : TheoryNode ctx)
    (hpos : Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_halt e))
    (hneg : ¬ Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_not_halt e))
    (hcomp : encode_not_halt e = ctx.Not (encode_halt e))
    (pick : OraclePick (S := ctx.toComplementaritySystem)
              encode_halt encode_not_halt e) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ pick.p ∈ T1.theory := by
  classical
  rcases pick.cert with ⟨hR, hpEq⟩ | ⟨hNR, hpEq⟩
  · -- positive branch: p = encode_halt e → Fork.left
    have hpivot : ctx.Truth (encode_halt e) := hpos hR
    let T1 := (Fork.ofPivot ctx T0 (encode_halt e)).left hpivot
    refine ⟨T1, Fork.ofPivot_edge_left ctx T0 (encode_halt e) hpivot, ?_⟩
    have hm : encode_halt e ∈ T1.theory :=
      Fork.ofPivot_pivot_mem_left ctx T0 (encode_halt e) hpivot
    simp only [T1, hpEq] at hm ⊢
    exact hm
  · -- negative branch: p = encode_not_halt e = Not pivot → Fork.right
    have hnot : ctx.Truth (encode_not_halt e) := hneg hNR
    have hnpivot : ctx.Truth (ctx.Not (encode_halt e)) := by
      rw [← hcomp]
      exact hnot
    let T1 := (Fork.ofPivot ctx T0 (encode_halt e)).right hnpivot
    refine ⟨T1, Fork.ofPivot_edge_right ctx T0 (encode_halt e) hnpivot, ?_⟩
    have hm : ctx.Not (encode_halt e) ∈ T1.theory :=
      Fork.ofPivot_not_pivot_mem_right ctx T0 (encode_halt e) hnpivot
    simp only [T1, hpEq, hcomp] at hm ⊢
    exact hm

/-!
## OraclePickCompl: Complementary OraclePick (design pattern)

When using the complementary two-sided, define `OraclePickCompl` so that
`hcomp := rfl` is automatic.
-/

/-- Complementary OraclePick: negative branch is definitionally `Not encode_halt`. -/
def OraclePickCompl (ctx : EnrichedContext Code PropT)
    (encode_halt : Code → PropT) (e : Code) :=
  OraclePick (S := ctx.toComplementaritySystem)
    encode_halt (fun e => ctx.Not (encode_halt e)) e

/-- With OraclePickCompl, the fork-step lemma simplifies (hcomp := rfl). -/
theorem oraclePickCompl_to_fork_step
    (ctx : EnrichedContext Code PropT)
    (encode_halt : Code → PropT)
    (e : Code)
    (T0 : TheoryNode ctx)
    (hpos : Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_halt e))
    (hneg : ¬ Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (ctx.Not (encode_halt e)))
    (pick : OraclePickCompl ctx encode_halt e) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ pick.p ∈ T1.theory :=
  oraclePick_to_fork_step ctx encode_halt (fun e => ctx.Not (encode_halt e)) e T0
    hpos hneg rfl pick

end RevHalt.Examples
