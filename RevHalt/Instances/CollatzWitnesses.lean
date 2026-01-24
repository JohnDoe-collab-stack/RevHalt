/-
  CollatzWitnesses.lean

  Phase 2 Skeleton Data:
  - Defines the *types* and *constants* required for the instance.
  - Implements Concrete Collatz Machine and Standard Kit.
  - Remaining logic (Witnesses, A0) is `sorry` (to be proved).
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics
import RevHalt.Base.Kit

namespace RevHalt.Instances

open RevHalt.Trilemma
open RevHalt

-- 1) Base Types
def PropT : Type := Nat
def Code : Type := Nat

-- 2) Parameters: Collatz Machine & Standard Kit

/-- Collatz Step Function -/
def CollatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Collatz Machine Trace: halts if it reaches 1. -/
def Machine (n : Code) : Trace :=
  fun k => ∃ m, m < k ∧ (Nat.iterate CollatzStep m n = 1)

/-- Standard Kit: projection to simple existence. -/
def StandardKit : RHKit :=
  { Proj := fun T => ∃ n, T n }

def K : RHKit := StandardKit
def encode_halt : Code → PropT := id
def Cn : Set PropT → Set PropT := id

-- Placeholder logic (Subject to filling in Phase 2)
def Provable : Set PropT → PropT → Prop := fun _ _ => False
def A0 : ThState (PropT := PropT) Provable Cn := sorry
def PAax : Set PropT := ∅

-- 4) Structural Proofs (Placeholders)
def hIdem : CnIdem Cn := sorry
def hProvCn : ProvClosedCn Provable Cn := sorry
def hMono : ProvRelMonotone Provable := sorry
def hCnExt : CnExtensive Cn := sorry

-- 5) Witnesses (Placeholders)
def witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC) := sorry

def witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC) := sorry

def witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB) := sorry

end RevHalt.Instances
