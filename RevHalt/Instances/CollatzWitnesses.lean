/-
  CollatzWitnesses.lean

  Phase 2 Data:
  - Defines the *types* and *constants* required for the instance.
  - Implements Concrete Collatz Machine and Standard Kit.
  - Bundles the remaining logic and witnesses as explicit data
    (no `sorry` / no `axiom` in this file).
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics
import RevHalt.Base.Kit
import RevHalt.Theory.TheoryDynamics_RouteII

namespace RevHalt.Instances

open RevHalt.Trilemma
open RevHalt

-- 1) Base Types
abbrev PropT : Type := Nat
abbrev Code : Type := Nat

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

open RevHalt.Categorical

lemma DetectsUpFixed_StandardKit_Aux : DetectsUpFixed StandardKit := by
  intro T _
  dsimp [StandardKit]
  rfl

abbrev K : RHKit := StandardKit

theorem DetectsUpFixed_StandardKit : DetectsUpFixed K := by
  intro T _
  rfl

def encode_halt : Code → PropT := id

-- 3) Standard Logic + Witnesses (bundle everything as data)
structure CollatzWitnessesData where
  -- Core logic
  Provable : Set PropT → PropT → Prop
  Cn : Set PropT → Set PropT
  PAax : Set PropT

  -- Structural proofs
  hIdem : CnIdem Cn
  hProvCn : ProvClosedCn Provable Cn
  hMono : ProvRelMonotone Provable
  hCnExt : CnExtensive Cn

  -- Initial state
  A0 : ThState (PropT := PropT) Provable Cn

  -- Standard logic properties (PA layer)
  SProvable_PA : PropT → Prop
  SNot_PA : PropT → PropT
  hSound_PA : ∀ Γ, Soundness Provable SProvable_PA Γ
  hNegComp_PA : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA
  hBarrier_PA : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False

  -- Witnesses
  witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC)
  witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC)
  witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)

-- ============================================================
-- 4) Option 1 (minimal, constructive core)
-- ============================================================

-- Minimal-but-nontrivial provability: closure under a concrete rule
-- Derivation rules:
--   1) Axiom: any element of Γ is provable.
--   2) Successor: if p is provable, then p+1 is provable.
inductive Derive (Γ : Set PropT) : PropT → Prop where
  | ax {p} : p ∈ Γ → Derive Γ p
  | succ {p} : Derive Γ p → Derive Γ (p + 1)

def Provable_min : Set PropT → PropT → Prop := fun Γ p => Derive Γ p

def Cn_min : Set PropT → Set PropT := fun Γ => { p | Derive Γ p }

-- Minimal PA axiom set: single axiom 0 (non-empty, constructive)
def PAax_min : Set PropT := {0}

lemma derive_mono {Γ Δ : Set PropT} (h : Γ ⊆ Δ) :
    ∀ p, Derive Γ p → Derive Δ p := by
  intro p hp
  induction hp with
  | ax hp' => exact Derive.ax (h hp')
  | succ hp' ih => exact Derive.succ ih

lemma derive_of_derive_cn {Γ : Set PropT} :
    ∀ p, Derive (Cn_min Γ) p → Derive Γ p := by
  intro p hp
  induction hp with
  | ax hp' => exact hp'
  | succ hp' ih => exact Derive.succ ih

lemma hIdem_min : CnIdem Cn_min := by
  intro Γ
  ext p
  constructor
  · intro hp
    exact derive_of_derive_cn (Γ := Γ) p hp
  · intro hp
    have hsubset : Γ ⊆ Cn_min Γ := by
      intro x hx
      exact Derive.ax hx
    exact derive_mono hsubset p hp

lemma hProvCn_min : ProvClosedCn Provable_min Cn_min := by
  intro Γ p hp
  exact derive_of_derive_cn (Γ := Γ) p hp

lemma hMono_min : ProvRelMonotone Provable_min := by
  intro Γ Δ h p hp
  exact derive_mono h p hp

lemma hCnExt_min : CnExtensive Cn_min := by
  intro Γ x hx
  exact Derive.ax hx

def A0_min : ThState (PropT := PropT) Provable_min Cn_min := by
  refine { Γ := Cn_min PAax_min, cn_closed := ?_, prov_closed := ?_ }
  · simpa using (hIdem_min (Γ := PAax_min))
  · intro p hp
    exact derive_of_derive_cn (Γ := PAax_min) p hp

-- Assumptions still needed to complete a concrete witness bundle
structure CollatzWitnessesAssumptions where
  SProvable_PA : PropT → Prop
  SNot_PA : PropT → PropT
  hSound_PA : ∀ Γ, Soundness Provable_min SProvable_PA Γ
  hNegComp_PA : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA
  hBarrier_PA : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False
  witBC : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
            (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.BC)
  witAC : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
            (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AC)
  witAB : CofinalWitness (PairPA (Provable := Provable_min) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn_min) (A0 := A0_min)
            (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AB)

-- ============================================================
-- 5) Phase D: derive witnesses from nontrivial hypotheses
-- ============================================================

def witness_of_forall {P : Nat → Prop} (h : ∀ n, P n) : CofinalWitness P :=
  fun N => ⟨N, Nat.le_refl N, h N⟩

lemma absorbable_min (Γ : Set PropT) : Absorbable (Provable := Provable_min) Γ := by
  intro p hp
  exact Derive.ax hp

lemma A_all_min :
    ∀ n, A (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) hIdem_min hProvCn_min n := by
  intro n p hp
  exact Derive.ax hp

lemma B_all_min
    (hPCdir : ProvClosedDirected Provable_min)
    (hω : CnOmegaContinuous Cn_min) :
    ∀ n, B (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) hIdem_min hProvCn_min n := by
  intro n
  simpa [B] using
    (omegaΓ_OmegaAdmissible (Provable := Provable_min) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn_min)
      (hCnExt := hCnExt_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min)
      (hPCdir := hPCdir) (hω := hω)
      (A0 := chainState (Provable := Provable_min) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn_min) hIdem_min hProvCn_min A0_min n))

lemma C_all_min
    {SProvable_PA : PropT → Prop} {SNot_PA : PropT → PropT}
    (hSound : ∀ Γ, Soundness Provable_min SProvable_PA Γ)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : ∀ e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False) :
    ∀ n, C (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) hIdem_min hProvCn_min n := by
  intro n
  have hNonempty :
      (S1Rel Provable_min K Machine encode_halt
        (omegaΓ Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min
          (chainState Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min A0_min n))).Nonempty :=
    frontier_nonempty_of_route_II (Provable := Provable_min) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (SProvable := SProvable_PA) (SNot := SNot_PA)
      (Γ := omegaΓ Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min
        (chainState Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min A0_min n))
      (hSound _) hNeg hDec hBar
  simpa [C, RouteIIAt] using hNonempty

lemma PA_at_all_min :
    ∀ n, PA_at (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min n := by
  intro n p hp
  -- PA_at is just subset at stage n
  have h0 : PAax_min ⊆ (chainState Provable_min K Machine encode_halt Cn_min hIdem_min hProvCn_min A0_min 0).Γ := by
    intro q hq
    -- A0_min.Γ = Cn_min PAax_min
    simpa using (hCnExt_min (Γ := PAax_min) hq)
  have hmono :=
    chainState_mono (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (hCnExt := hCnExt_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min)
      (A0 := A0_min) 0 n (Nat.zero_le n)
  exact hmono (h0 hp)

lemma PairPA_all_min_BC
    (hPCdir : ProvClosedDirected Provable_min)
    (hω : CnOmegaContinuous Cn_min)
    {SProvable_PA : PropT → Prop} {SNot_PA : PropT → PropT}
    (hSound : ∀ Γ, Soundness Provable_min SProvable_PA Γ)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : ∀ e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False) :
    ∀ n, PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.BC n := by
  intro n
  refine ⟨?_, PA_at_all_min n⟩
  exact ⟨B_all_min hPCdir hω n, C_all_min hSound hNeg hDec hBar n⟩

lemma PairPA_all_min_AC
    {SProvable_PA : PropT → Prop} {SNot_PA : PropT → PropT}
    (hSound : ∀ Γ, Soundness Provable_min SProvable_PA Γ)
    (hNeg   : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA)
    (hDec   : ∀ e, Decidable (SProvable_PA (encode_halt e)))
    (hBar   : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False) :
    ∀ n, PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AC n := by
  intro n
  refine ⟨?_, PA_at_all_min n⟩
  exact ⟨A_all_min n, C_all_min hSound hNeg hDec hBar n⟩

lemma PairPA_all_min_AB
    (hPCdir : ProvClosedDirected Provable_min)
    (hω : CnOmegaContinuous Cn_min) :
    ∀ n, PairPA (Provable := Provable_min) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn_min) (A0 := A0_min) (hIdem := hIdem_min) (hProvCn := hProvCn_min) PAax_min Mode.AB n := by
  intro n
  refine ⟨?_, PA_at_all_min n⟩
  exact ⟨A_all_min n, B_all_min hPCdir hω n⟩

structure CollatzWitnessesAssumptionsD where
  SProvable_PA : PropT → Prop
  SNot_PA : PropT → PropT
  hSound_PA : ∀ Γ, Soundness Provable_min SProvable_PA Γ
  hNegComp_PA : NegativeComplete K Machine encode_halt SProvable_PA SNot_PA
  hDec_PA : ∀ e, Decidable (SProvable_PA (encode_halt e))
  hBarrier_PA : (∀ e, Decidable (SProvable_PA (encode_halt e))) → False
  hPCdir : ProvClosedDirected Provable_min
  hω : CnOmegaContinuous Cn_min

def CollatzWitnessesAssumptionsD.toWitnesses (A : CollatzWitnessesAssumptionsD) :
    CollatzWitnessesAssumptions := by
  refine {
    SProvable_PA := A.SProvable_PA
    SNot_PA := A.SNot_PA
    hSound_PA := A.hSound_PA
    hNegComp_PA := A.hNegComp_PA
    hBarrier_PA := A.hBarrier_PA
    witBC := witness_of_forall (PairPA_all_min_BC A.hPCdir A.hω A.hSound_PA A.hNegComp_PA A.hDec_PA A.hBarrier_PA)
    witAC := witness_of_forall (PairPA_all_min_AC A.hSound_PA A.hNegComp_PA A.hDec_PA A.hBarrier_PA)
    witAB := witness_of_forall (PairPA_all_min_AB A.hPCdir A.hω)
  }

def CollatzWitnessesMinimal (A : CollatzWitnessesAssumptions) : CollatzWitnessesData := by
  refine {
    Provable := Provable_min
    Cn := Cn_min
    PAax := PAax_min
    hIdem := hIdem_min
    hProvCn := hProvCn_min
    hMono := hMono_min
    hCnExt := hCnExt_min
    A0 := A0_min
    SProvable_PA := A.SProvable_PA
    SNot_PA := A.SNot_PA
    hSound_PA := A.hSound_PA
    hNegComp_PA := A.hNegComp_PA
    hBarrier_PA := A.hBarrier_PA
    witBC := A.witBC
    witAC := A.witAC
    witAB := A.witAB
  }

end RevHalt.Instances
