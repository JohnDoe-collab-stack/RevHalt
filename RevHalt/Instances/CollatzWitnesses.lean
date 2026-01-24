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

-- 3) Trivial Logic (Provability = Membership)
def Provable : Set PropT → PropT → Prop := fun Γ p => p ∈ Γ
def Cn : Set PropT → Set PropT := id
def PAax : Set PropT := ∅

-- Structural proofs for Trivial Logic
lemma hIdem_proof (Γ : Set PropT) : Cn (Cn Γ) = Cn Γ := rfl
lemma hProvCn_proof (Γ : Set PropT) (p : PropT) : Provable (Cn Γ) p → p ∈ Cn Γ := fun h => h
lemma hMono_proof (Γ Δ : Set PropT) (h : Γ ⊆ Δ) (p : PropT) : Provable Γ p → Provable Δ p := fun hp => h hp
lemma hCnExt_proof (Γ : Set PropT) : Γ ⊆ Cn Γ := fun _ h => h

def hIdem : CnIdem Cn := hIdem_proof
def hProvCn : ProvClosedCn Provable Cn := hProvCn_proof
def hMono : ProvRelMonotone Provable := hMono_proof
def hCnExt : CnExtensive Cn := hCnExt_proof

-- Initial State A0
def A0 : ThState (PropT := PropT) Provable Cn :=
{ Γ := ∅
  cn_closed := rfl
  prov_closed := fun _ h => h
}

-- Helper: Construct witness from eventual truth (Constructive Data)
-- Requires finding the bound N0 explicitly (Subtype).
def witness_of_eventually
  {P : Nat → Prop}
  (h : { N0 // ∀ n, N0 ≤ n → P n }) : CofinalWitness P := by
  let ⟨N0, hN0⟩ := h
  intro N
  refine ⟨Nat.max N N0, ?_, ?_⟩
  · exact Nat.le_max_left _ _
  · have : N0 ≤ Nat.max N N0 := Nat.le_max_right _ _
    exact hN0 _ this

-- 5) Witnesses
-- We satisfy the type signature using the constructive helper.
-- The premise (eventual truth of horns) remains a proof obligation using `sorry`.

def witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC) :=
  witness_of_eventually (sorry)

def witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC) :=
  witness_of_eventually (sorry)

def witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB) :=
  witness_of_eventually (sorry)

end RevHalt.Instances
