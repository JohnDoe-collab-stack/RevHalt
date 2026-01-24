/-
  GenericExtinction.lean

  Pure Logic Module:
  - Contains strictly generic Trilemma logic.
  - No imports of Collatz.
  - Defines the `CollatzInstance` structure for Phase 2 implementation.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA
import RevHalt.Theory.TheoryDynamics

namespace RevHalt.Trilemma.Generic

open Set

universe u

-- ============================================================
-- 1) THE GENERIC PROBLEM DEFINITION
-- ============================================================

-- Pont (Generic Definition)
def PA_implies_RouteIIAt
    {PropT : Type u} {Code : Type u}
    (Provable : Set PropT → PropT → Prop)
    (K : RHKit)
    (Machine : Code → Trace)
    (encode_halt : Code → PropT)
    (Cn : Set PropT → Set PropT)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (PAax : Set PropT) : Prop :=
  ∀ t,
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t →
    RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
        (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t))

-- But générique : extinction AB pour sigma
def EventuallyNotAB (sigma : Nat → Mode) : Prop :=
  ∃ N, ∀ k, N ≤ k → sigma k ≠ Mode.AB


-- ============================================================
-- 2) THE INSTANCE STRUCTURE (Requirements for Phase 2)
-- ============================================================

structure CollatzInstance where
  PropT : Type u
  Code : Type u
  Provable : Set PropT → PropT → Prop
  K : RHKit
  Machine : Code → Trace
  encode_halt : Code → PropT
  Cn : Set PropT → Set PropT
  A0 : ThState (PropT := PropT) Provable Cn
  PAax : Set PropT

  -- Structural Axioms
  hIdem : CnIdem Cn
  hProvCn : ProvClosedCn Provable Cn
  hMono : ProvRelMonotone Provable
  hCnExt : CnExtensive Cn

  -- Witnesses for standard modes
  witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC)
  witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC)
  witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
            (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
            (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB)

  -- The Consistency Bridge
  bridge : PA_implies_RouteIIAt Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax


-- ============================================================
-- 3) THE GENERIC PROOF (Generic Logic)
-- ============================================================

section Proof

-- Explicitly pass (I : CollatzInstance) everywhere to avoid variable lookup issues in signatures
-- Also use CollatzInstance.Field accessor in types

lemma chainState_mono
    (I : CollatzInstance)
    {t u : Nat} (htu : t ≤ u) :
    (chainState (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
       (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) t).Γ ⊆
    (chainState (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
       (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) u).Γ := by
  induction htu with
  | refl => exact Set.Subset.refl _
  | step h ih =>
      apply Set.Subset.trans ih
      apply chainState_step_hom (Provable := I.Provable) (K := I.K) (Machine := I.Machine)
        (encode_halt := I.encode_halt) (Cn := I.Cn)
        I.hIdem I.hProvCn I.hCnExt I.A0

lemma PA_at_mono
    (I : CollatzInstance)
    {t u : Nat} (htu : t ≤ u)
    (hPA : PA_at (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
            (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) I.PAax t) :
    PA_at (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
      (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) I.PAax u := by
  exact Set.Subset.trans hPA (chainState_mono I htu)

lemma PA_Eventually_of_exists
    (I : CollatzInstance)
    {t0 : Nat}
    (hPA0 :
      PA_at (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
        (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) I.PAax t0) :
    ∃ N, ∀ n, N ≤ n →
      PA_at (Provable := I.Provable) (K := I.K) (Machine := I.Machine) (encode_halt := I.encode_halt)
        (Cn := I.Cn) (A0 := I.A0) (hIdem := I.hIdem) (hProvCn := I.hProvCn) I.PAax n := by
  refine ⟨t0, ?_⟩
  intro n hn
  exact PA_at_mono I hn hPA0

/-- THEOREM: Given a valid instance I and ANY sigma compatible with it. -/
theorem eventuallyNotAB_of_instance
    (sigma : Nat → Mode)
    (I : CollatzInstance) :
    EventuallyNotAB sigma := by

  -- Unpack Instance fields for clarity
  let Provable := I.Provable
  let K := I.K
  let Machine := I.Machine
  let encode_halt := I.encode_halt
  let Cn := I.Cn
  let A0 := I.A0
  let hIdem := I.hIdem
  let hProvCn := I.hProvCn
  let PAax := I.PAax
  let hMono := I.hMono
  let hCnExt := I.hCnExt
  let witBC := I.witBC
  let witAC := I.witAC
  let witAB := I.witAB
  let hBridge := I.bridge

  -- 0) Extract PA
  rcases witBC 0 with ⟨t0, _, ht0⟩
  have hPA0 : PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t0 := ht0.2

  -- 1) Monotonicity
  rcases (PA_Eventually_of_exists I hPA0) with ⟨N, hPA⟩

  -- 2) Simple Witnesses
  let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.BC witBC
  let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AC witAC
  let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (hIdem := hIdem) (hProvCn := hProvCn) PAax Mode.AB witAB

  -- 3) Absurdity on subsequences
  refine ⟨N, ?_⟩
  intro k hkN hkAB

  let t := times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigma) hIdem hProvCn wBC wAC wAB k

  let f : Nat → Nat := fun m =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigma) hIdem hProvCn wBC wAC wAB m

  have hstep : StrictStep f := by
    intro m
    simpa [f] using (times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
        wBC wAC wAB m)

  have hk_le_t : k ≤ t := by
    have hk_le_fk : k ≤ f k := le_of_strictStep f hstep k
    simpa [t, f] using hk_le_fk

  have hN_le_t : N ≤ t := Nat.le_trans hkN hk_le_t

  have hPA_t : PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax t := hPA t hN_le_t

  have hRoute := hBridge t hPA_t

  have hNotRoute_raw := strict_subseq_horns (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      (sigma := sigma) hMono hCnExt hIdem hProvCn
      wBC wAC wAB k

  have hNotRoute : ¬ RouteIIAt (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (omegaΓ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (hIdem := hIdem) (hProvCn := hProvCn)
          (chainState (Provable := Provable) (K := K) Machine (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) t)) := by
    simpa [t, hkAB] using hNotRoute_raw

  exact hNotRoute hRoute

end Proof
end RevHalt.Trilemma.Generic
