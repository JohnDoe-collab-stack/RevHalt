/-
  CollatzWitnesses.lean

  Phase 2 Skeleton Data:
  - Defines the *types* and *constants* required for the instance.
  - Currently implemented as Computable Placeholders (using `sorry` or dummy types).
  - This allows compilation without `noncomputable`.
  - Goal of Phase 2: Replace `sorry` with actual logic.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics

namespace RevHalt.Instances

open RevHalt.Trilemma

-- 1) Base Types (Placeholder: Nat)
def PropT : Type := Nat
def Code : Type := Nat

-- 2) Parameters
def Provable : Set PropT → PropT → Prop := fun _ _ => False -- Dummy
def K : RHKit := sorry -- Placeholder
def Machine : Code → Trace := fun _ _ => False -- Dummy
def encode_halt : Code → PropT := fun c => c -- Dummy
def Cn : Set PropT → Set PropT := id -- Dummy

-- 3) Initial State
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
