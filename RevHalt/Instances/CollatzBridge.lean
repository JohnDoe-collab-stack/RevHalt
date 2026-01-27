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

-- Bridge assumptions packaged as data (no axioms)
structure CollatzBridgeAssumptions (W : CollatzWitnessesData) where
  -- Encoding of Universal code into PropT
  encode_U : UCode → PropT

  -- Richness Bridge:
  -- Empty Collatz frontier => Empty Universal frontier (same Γ)
  richness_bridge_axiom {Γ : Set PropT} :
    S1Rel W.Provable K Machine encode_halt Γ = ∅ →
    S1Rel W.Provable K UMachine encode_U Γ = ∅

  -- Universal Machine hypotheses (Route II / T2)
  hSound_U : ∀ Γ, Soundness W.Provable W.SProvable_PA Γ
  hNegComp_U : NegativeComplete K UMachine encode_U W.SProvable_PA W.SNot_PA
  hTotal_U : ∀ e, W.SProvable_PA (encode_U e) ∨ W.SProvable_PA (W.SNot_PA (encode_U e))
  f_U : UCode → (Nat →. Nat)
  hf_U : Partrec (fun p : UCode × Nat => f_U p.1 p.2)
  hsemidec_U :
    ∀ c, W.SProvable_PA (W.SNot_PA (encode_U c)) ↔ (∃ x : Nat, x ∈ (f_U c) 0)

  -- Minimal ImpossibleSystem coherence for PA layer
  S_PA_consistent : ¬ W.SProvable_PA (0 : Nat)
  S_PA_absurd :
    ∀ p, W.SProvable_PA p → W.SProvable_PA (W.SNot_PA p) → W.SProvable_PA (0 : Nat)

-- 4) The Proof

theorem bridge_proof
    (W : CollatzWitnessesData)
    (B : CollatzBridgeAssumptions W) :
    PA_implies_RouteIIAt
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := W.Cn) (A0 := W.A0) (hIdem := W.hIdem) (hProvCn := W.hProvCn) W.PAax := by
  intro t hPA
  -- Goal: RouteIIAt (omegaΓ t)
  -- Def: (S1Rel Collatz ...).Nonempty
  rw [RouteIIAt]
  by_contra hEmptyCollatz
  rw [Set.not_nonempty_iff_eq_empty] at hEmptyCollatz

  -- 1) Use Bridge to switch to Universal
  have hEmptyUniversal : S1Rel W.Provable K UMachine B.encode_U
      (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
        (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)) = ∅ :=
    B.richness_bridge_axiom hEmptyCollatz

  -- 2) Use T2 on Universal to derive False
  -- We need to satisfy T2 hypotheses.
  -- PA_at t implies we have PA axioms?
  -- Actually, frontier_empty_T2_full takes S : ImpossibleSystem.
  -- We construct S from SProvable_PA.
  -- Axiom: SProvable_PA forms an ImpossibleSystem (Standard Arithmetic).
  -- We'll assume the ImpossibleSystem structure exists for PA.
  let S_PA : ImpossibleSystem PropT := {
    Provable := W.SProvable_PA
    FalseT := (0 : Nat) -- PropT is Nat
    Not := W.SNot_PA
    consistent := B.S_PA_consistent
    absurd := B.S_PA_absurd
  }

  -- We need Soundness regarding the specific Γ = omegaΓ t.
  -- hSound_U is global "∀ Γ", so it applies.
  let Γ_omega := omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
    (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)
  have hSound_omega : Soundness W.Provable S_PA.Provable Γ_omega := B.hSound_U Γ_omega

  -- Apply T2
  apply frontier_empty_T2_full (Provable := W.Provable) (K := K) (encode_halt := B.encode_U)
    S_PA
    (DetectsUpFixed_StandardKit) -- K is StandardKit
    hEmptyUniversal
    hSound_omega
    B.hNegComp_U
    B.hTotal_U
    B.f_U B.hf_U B.hsemidec_U

-- 5) Construct the Instance Field
-- We need to provide the 'bridge' field for CollatzInstance.
-- But CollatzInstance is defined in GenericExtinction generic section.
-- Here we are in Instances namespace.
-- We will export this theorem to be used in ConcreteCollatz.lean.

end RevHalt.Instances
