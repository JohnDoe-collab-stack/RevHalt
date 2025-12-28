/-
  RevHalt.Dynamics.Core.Fork2

  ═══════════════════════════════════════════════════════════════════════════════
  THREE-LEVEL BIFURCATION HIERARCHY
  ═══════════════════════════════════════════════════════════════════════════════
  1. BinaryStep: two pivots, conditional branches, NO exclusion
  2. Fork2: two pivots + soundness exclusion
  3. Fork: pivot / Not pivot + automatic exclusion (existing Fork.lean)

  OraclePick maps to:
  - BinaryStep: ALWAYS (no hypothesis)
  - Fork2: if exclusion is proven (or derived from complementarity)
  - Fork: if Complementary (encode_not_halt = Not encode_halt)
  ═══════════════════════════════════════════════════════════════════════════════
-/

import RevHalt.Dynamics.Core.Node
import RevHalt.Dynamics.Core.Graph
import RevHalt.Dynamics.Core.Fork
import RevHalt.Bridge.ComplementarityAPI

namespace RevHalt.Dynamics.Core

open Set

variable {Code PropT : Type}

/-!
## Level 1: BinaryStep (no exclusion)

Two arbitrary pivots with conditional branches. No soundness exclusion.
OraclePick ALWAYS gives a BinaryStep.
-/

/-- BinaryStep = bifurcation with two pivots, NO exclusion guarantee. -/
structure BinaryStep (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx) where
  pivot_left : PropT
  pivot_right : PropT
  mkLeft : ctx.Truth pivot_left → TheoryNode ctx
  mkRight : ctx.Truth pivot_right → TheoryNode ctx

namespace BinaryStep

variable {ctx : EnrichedContext Code PropT} {T0 : TheoryNode ctx}

/-- Canonical BinaryStep on two pivots. -/
def ofPivots (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p_left p_right : PropT) : BinaryStep ctx T0 where
  pivot_left := p_left
  pivot_right := p_right
  mkLeft := fun hp =>
    { theory := Extend T0.theory p_left
      sound := fun q hq => by
        simp only [mem_Extend_iff] at hq
        rcases hq with hqT0 | rfl
        · exact T0.sound q hqT0
        · exact hp }
  mkRight := fun hq =>
    { theory := Extend T0.theory p_right
      sound := fun r hr => by
        simp only [mem_Extend_iff] at hr
        rcases hr with hrT0 | rfl
        · exact T0.sound r hrT0
        · exact hq }

def left (b : BinaryStep ctx T0) (hp : ctx.Truth b.pivot_left) : TheoryNode ctx :=
  b.mkLeft hp

def right (b : BinaryStep ctx T0) (hq : ctx.Truth b.pivot_right) : TheoryNode ctx :=
  b.mkRight hq

/-- Edge from T0 to left branch. -/
theorem ofPivots_edge_left (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p_left p_right : PropT) (hp : ctx.Truth p_left) :
    Edge ctx T0 ((ofPivots ctx T0 p_left p_right).left hp) := by
  apply Edge.transport_target (Edge.of_move (Move.extend p_left hp) T0)
  simp only [left, ofPivots, Move.apply_extend_theory]

/-- Edge from T0 to right branch. -/
theorem ofPivots_edge_right (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p_left p_right : PropT) (hq : ctx.Truth p_right) :
    Edge ctx T0 ((ofPivots ctx T0 p_left p_right).right hq) := by
  apply Edge.transport_target (Edge.of_move (Move.extend p_right hq) T0)
  simp only [right, ofPivots, Move.apply_extend_theory]

end BinaryStep

/-!
## Level 2: Fork2 (with exclusion)

BinaryStep + soundness exclusion.
OraclePick gives Fork2 ONLY if exclusion is proven.
-/

/-- Fork2 = BinaryStep + exclusion. -/
structure Fork2 (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    extends BinaryStep ctx T0 where
  exclusion :
    ¬ (TheorySound ctx (Extend T0.theory pivot_left) ∧
       TheorySound ctx (Extend T0.theory pivot_right))

namespace Fork2

variable {ctx : EnrichedContext Code PropT} {T0 : TheoryNode ctx}

/-- Promote BinaryStep to Fork2 with exclusion proof. -/
def ofBinaryStep (b : BinaryStep ctx T0)
    (h_excl : ¬ (TheorySound ctx (Extend T0.theory b.pivot_left) ∧
                 TheorySound ctx (Extend T0.theory b.pivot_right))) :
    Fork2 ctx T0 :=
  { b with exclusion := h_excl }

/-- Canonical Fork2 on two pivots with exclusion. -/
def ofPivots (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p_left p_right : PropT)
    (h_excl : ¬ (TheorySound ctx (Extend T0.theory p_left) ∧
                 TheorySound ctx (Extend T0.theory p_right))) :
    Fork2 ctx T0 :=
  ofBinaryStep (BinaryStep.ofPivots ctx T0 p_left p_right) h_excl

end Fork2

/-!
## Complementarity Condition
-/

/-- Syntactic complementarity: q is exactly Not p. -/
def Complementary (ctx : EnrichedContext Code PropT) (p q : PropT) : Prop :=
  q = ctx.Not p

/-- With complementarity, exclusion is automatic. -/
theorem exclusion_of_complementary
    (ctx : EnrichedContext Code PropT) (T0 : TheoryNode ctx)
    (p q : PropT) (hcomp : Complementary ctx p q) :
    ¬ (TheorySound ctx (Extend T0.theory p) ∧ TheorySound ctx (Extend T0.theory q)) := by
  rw [hcomp]
  exact EnrichedContext.not_both_sound_extend_p_and_not (ctx := ctx) (T0 := T0.theory) (p := p)

/-!
## OraclePick → BinaryStep (ALWAYS valid)
-/

/-- OraclePick ALWAYS gives a BinaryStep extension. No exclusion. -/
theorem oraclePick_to_binaryStep
    (ctx : EnrichedContext Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code)
    (T0 : TheoryNode ctx)
    (hpos : Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_halt e))
    (hneg : ¬ Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_not_halt e))
    (pick : OraclePick (S := ctx.toComplementaritySystem) encode_halt encode_not_halt e) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ pick.p ∈ T1.theory := by
  let b := BinaryStep.ofPivots ctx T0 (encode_halt e) (encode_not_halt e)
  rcases pick.cert with ⟨hR, hpEq⟩ | ⟨hNR, hpEq⟩
  · have hp : ctx.Truth (encode_halt e) := hpos hR
    refine ⟨b.left hp, BinaryStep.ofPivots_edge_left ctx T0 _ _ hp, ?_⟩
    simp only [BinaryStep.left, BinaryStep.ofPivots, mem_Extend_iff]
    right
    rw [hpEq]
    exact Set.mem_singleton _
  · have hq : ctx.Truth (encode_not_halt e) := hneg hNR
    refine ⟨b.right hq, BinaryStep.ofPivots_edge_right ctx T0 _ _ hq, ?_⟩
    simp only [BinaryStep.right, BinaryStep.ofPivots, mem_Extend_iff]
    right
    rw [hpEq]
    exact Set.mem_singleton _

/-!
## OraclePick + Complementary → Fork (via Fork.ofPivot)
-/

/-- OraclePick + Complementary gives a Fork extension with exclusion. -/
theorem oraclePick_to_fork_of_complementary
    (ctx : EnrichedContext Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (e : Code)
    (T0 : TheoryNode ctx)
    (hpos : Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_halt e))
    (hneg : ¬ Rev0_K ctx.K (ctx.Machine e) → ctx.Truth (encode_not_halt e))
    (hcomp : Complementary ctx (encode_halt e) (encode_not_halt e))
    (pick : OraclePick (S := ctx.toComplementaritySystem) encode_halt encode_not_halt e) :
    ∃ T1 : TheoryNode ctx, Edge ctx T0 T1 ∧ pick.p ∈ T1.theory := by
  let f := Fork.ofPivot ctx T0 (encode_halt e)
  rcases pick.cert with ⟨hR, hpEq⟩ | ⟨hNR, hpEq⟩
  · -- Left branch: pick.p = encode_halt e
    have hp : ctx.Truth (encode_halt e) := hpos hR
    refine ⟨f.left hp, Fork.ofPivot_edge_left ctx T0 (encode_halt e) hp, ?_⟩
    have hm := Fork.ofPivot_pivot_mem_left ctx T0 (encode_halt e) hp
    -- goal: pick.p ∈ T1.theory, hm: encode_halt e ∈ T1.theory
    simpa [hpEq] using hm
  · -- Right branch: pick.p = encode_not_halt e = Not (encode_halt e)
    have hq : ctx.Truth (encode_not_halt e) := hneg hNR
    have hnpivot : ctx.Truth (ctx.Not (encode_halt e)) := by
      rw [← hcomp]; exact hq
    refine ⟨f.right hnpivot, Fork.ofPivot_edge_right ctx T0 (encode_halt e) hnpivot, ?_⟩
    have hm := Fork.ofPivot_not_pivot_mem_right ctx T0 (encode_halt e) hnpivot
    -- hm: Not (encode_halt e) ∈ T1.theory
    -- goal: pick.p ∈ T1.theory
    -- hpEq: pick.p = encode_not_halt e
    -- hcomp: encode_not_halt e = ctx.Not (encode_halt e)
    rw [hpEq, hcomp]
    exact hm

/-!
## Fork.toFork2 / Fork.toBinaryStep
-/

/-- Fork → Fork2. -/
def Fork.toFork2 {ctx : EnrichedContext Code PropT} {T0 : TheoryNode ctx}
    (f : Fork ctx T0) : Fork2 ctx T0 where
  pivot_left := f.pivot
  pivot_right := ctx.Not f.pivot
  mkLeft := f.mkLeft
  mkRight := f.mkRight
  exclusion := f.exclusion

/-- Fork → BinaryStep (drops exclusion). -/
def Fork.toBinaryStep {ctx : EnrichedContext Code PropT} {T0 : TheoryNode ctx}
    (f : Fork ctx T0) : BinaryStep ctx T0 where
  pivot_left := f.pivot
  pivot_right := ctx.Not f.pivot
  mkLeft := f.mkLeft
  mkRight := f.mkRight

end RevHalt.Dynamics.Core
