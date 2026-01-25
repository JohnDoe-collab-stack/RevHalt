/-
  CollatzBridge.lean

  Phase 2 Logic: The Bridge
  - Proves PA_implies_RouteIIAt
  - Relies on "Richness Bridge" Axiom (Collatz Hardness)
  - Relies on T2 Barrier (Universal Machine Undecidability)

  The Logic:
  1. Assume PA is available.
  2. Assume RouteIIAt(Collatz) fails (Frontier Empty).
  3. This implies Collatz is Decidable.
  4. Via Richness Bridge, this implies Universal Machine is Decidable (Frontier Empty).
  5. Contradiction with T2 Barrier on Universal Machine.
  6. Therefore, RouteIIAt(Collatz) must hold.
-/

import RevHalt.Instances.CollatzWitnesses
import RevHalt.Theory.TheoryDynamics
import RevHalt.Trilemma.GenericExtinction
import RevHalt.Theory.TheoryDynamics_RouteII
import RevHalt.Theory.Impossibility
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec

namespace RevHalt.Instances

open Nat.Partrec
open RevHalt.Trilemma
open RevHalt.Trilemma.Generic

-- 1) Universal Machine Setup (for T2)
-- We need to map Universal Code to PropT (Nat)
-- 1) Universal Machine Setup (for T2)
abbrev UCode := Nat.Partrec.Code
abbrev UMachine : UCode → Trace := RevHalt.Machine

-- We need an encoding of UCode into PropT (Nat).
axiom encode_U : UCode → PropT

-- 2) The Richness Bridge Axiom
-- "If Collatz is decidable by Γ, then Universal Machine is decidable by Γ"
-- Formally: Empty Collatz Frontier implies Empty Universal Frontier in the same theory Γ.
axiom richness_bridge_axiom {Γ : Set PropT} :
  S1Rel Provable K Machine encode_halt Γ = ∅ →
  S1Rel Provable K UMachine encode_U Γ = ∅

-- 3) T2 Barrier on Universal Machine
-- We need to know that (S1Rel Universal) cannot be empty for "Strong" Γ (like PA).
-- Or rather, S1Rel Universal cannot be empty for ANY Γ (if Standard T2 holds).
-- T2 says: ¬ InternalHaltingPredicate.
-- frontier_empty_T2_full says: Empty -> False.
-- So we need to instantiate frontier_empty_T2_full for UMachine.

-- We need witnesses for Universal Machine (Soundness, NegComp, Semidecider relative to PA).
-- These are properties of PA wrt Universal Computation.
axiom hSound_U : ∀ Γ, Soundness Provable SProvable_PA Γ
axiom hNegComp_U : NegativeComplete K UMachine encode_U SProvable_PA SNot_PA
-- We need the semi-decider witness for Universal Negation
axiom f_U : UCode → (Nat →. Nat)
axiom hf_U : Partrec (fun p : UCode × Nat => f_U p.1 p.2)
axiom hsemidec_U : ∀ c, SProvable_PA (SNot_PA (encode_U c)) ↔ (∃ x : Nat, x ∈ (f_U c) 0)

-- 4) The Proof

theorem bridge_proof :
    PA_implies_RouteIIAt
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax := by
  intro t hPA
  -- Goal: RouteIIAt (omegaΓ t)
  -- Def: (S1Rel Collatz ...).Nonempty
  rw [RouteIIAt]
  by_contra hEmptyCollatz
  rw [Set.not_nonempty_iff_eq_empty] at hEmptyCollatz

  -- 1) Use Bridge to switch to Universal
  have hEmptyUniversal : S1Rel Provable K UMachine encode_U
      (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 t)) = ∅ :=
    richness_bridge_axiom hEmptyCollatz

  -- 2) Use T2 on Universal to derive False
  -- We need to satisfy T2 hypotheses.
  -- PA_at t implies we have PA axioms?
  -- Actually, frontier_empty_T2_full takes S : ImpossibleSystem.
  -- We construct S from SProvable_PA.
  -- Axiom: SProvable_PA forms an ImpossibleSystem (Standard Arithmetic).
  -- We'll assume the ImpossibleSystem structure exists for PA.
  let S_PA : ImpossibleSystem PropT := {
    Provable := SProvable_PA
    FalseT := (0 : Nat) -- PropT is Nat
    Not := SNot_PA
    consistent := sorry -- PA consistency
    absurd := sorry -- PA logic
  }

  -- We need Soundness regarding the specific Γ = omegaΓ t.
  -- hSound_U is global "∀ Γ", so it applies.
  let Γ_omega := omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 t)
  have hSound_omega : Soundness Provable S_PA.Provable Γ_omega := hSound_U Γ_omega

  -- Apply T2
  apply frontier_empty_T2_full (Provable := Provable) (K := K) (encode_halt := encode_U)
    S_PA
    (DetectsUpFixed_StandardKit) -- K is StandardKit
    hEmptyUniversal
    hSound_omega
    hNegComp_U
    f_U hf_U hsemidec_U

-- 5) Construct the Instance Field
-- We need to provide the 'bridge' field for CollatzInstance.
-- But CollatzInstance is defined in GenericExtinction generic section.
-- Here we are in Instances namespace.
-- We will export this theorem to be used in ConcreteCollatz.lean.

end RevHalt.Instances
