/-
  CollatzBridge.lean

  Phase 2 Logic: The Bridge (constructive, but allows classical T2 lemmas).
  - Proves PA_implies_RouteIIAt using an explicit reduction parameterized by
    (encode_U, compile, hEncode, hSim) plus T2 hypotheses.
  - Also provides a purely dynamic fallback (optional).
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
open RevHalt

-- 1) Universal Machine Setup (for T2)
abbrev UCode := Nat.Partrec.Code
abbrev UMachine : UCode → Trace := RevHalt.Machine

-- Bridge assumptions packaged as data (no axioms)
structure CollatzBridgeAssumptions (W : CollatzWitnessesData) where
  -- Encoding of Universal code into PropT
  encode_U : UCode → PropT

  -- Concrete reduction UMachine -> Collatz machine, stated at the Rev observation layer.
  --
  -- The project’s “Rev” principle only allows using the `up`-geometry of traces:
  -- if two traces are observationally equivalent (UpEqv), then `Rev0_K` cannot
  -- distinguish them.
  compile : UCode → Code
  hEncode : ∀ c, encode_U c = encode_halt (compile c)
  hUpEqv : ∀ c, UpEqv (UMachine c) (Machine (compile c))

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

def CollatzBridgeAssumptions_of_AssumptionsD
    (A : CollatzWitnessesAssumptionsD)
    (encode_U : UCode → PropT)
    (compile : UCode → Code)
    (hEncode : ∀ c, encode_U c = encode_halt (compile c))
    (hUpEqv :
      ∀ c, UpEqv (UMachine c) (Machine (compile c)))
    (hSound_U : ∀ Γ, Soundness (CollatzWitnessesData_of_AssumptionsD A).Provable
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA Γ)
    (hNegComp_U : NegativeComplete K UMachine encode_U
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
      (CollatzWitnessesData_of_AssumptionsD A).SNot_PA)
    (hTotal_U : ∀ e, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (encode_U e) ∨
      (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U e)))
    (f_U : UCode → (Nat →. Nat))
    (hf_U : Partrec (fun p : UCode × Nat => f_U p.1 p.2))
    (hsemidec_U :
      ∀ c, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
        ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA (encode_U c)) ↔
        (∃ x : Nat, x ∈ (f_U c) 0))
    (S_PA_consistent : ¬ (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat))
    (S_PA_absurd :
      ∀ p, (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA p →
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA
          ((CollatzWitnessesData_of_AssumptionsD A).SNot_PA p) →
        (CollatzWitnessesData_of_AssumptionsD A).SProvable_PA (0 : Nat)) :
    CollatzBridgeAssumptions (CollatzWitnessesData_of_AssumptionsD A) :=
  { encode_U := encode_U
    compile := compile
    hEncode := hEncode
    hUpEqv := hUpEqv
    hSound_U := hSound_U
    hNegComp_U := hNegComp_U
    hTotal_U := hTotal_U
    f_U := f_U
    hf_U := hf_U
    hsemidec_U := hsemidec_U
    S_PA_consistent := S_PA_consistent
    S_PA_absurd := S_PA_absurd }

-- 4) The Proof (Bridge)
theorem bridge_proof
    (W : CollatzWitnessesData)
    (B : CollatzBridgeAssumptions W) :
    PA_implies_RouteIIAt
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := W.Cn) (A0 := W.A0) (hIdem := W.hIdem) (hProvCn := W.hProvCn) W.PAax := by
  intro t _hPA
  -- Goal: RouteIIAt (omegaΓ t)
  rw [RouteIIAt]
  by_contra hEmptyCollatz
  rw [Set.not_nonempty_iff_eq_empty] at hEmptyCollatz

  -- 1) Use the concrete reduction to switch emptiness from Collatz to Universal.
  have hEmptyUniversal :
      S1Rel W.Provable K UMachine B.encode_U
        (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
          (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)) = ∅ :=
    by
      -- Show emptiness of U frontier from Collatz frontier emptiness (same Γ).
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨c, hpEq, hRev, hNprov⟩ := hp
      have hRev' : Rev0_K K (Machine (B.compile c)) := by
        -- Transport the Rev verdict along the UpEqv simulation.
        have hIff :
            Rev0_K K (UMachine c) ↔ Rev0_K K (Machine (B.compile c)) :=
          revK_congr_of_UpEqv (K := K) DetectsUpFixed_StandardKit (B.hUpEqv c)
        exact hIff.mp hRev
      have hNprov' : ¬ W.Provable
          (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
            (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t))
          (encode_halt (B.compile c)) := by
        simpa [B.hEncode c] using hNprov
      have hMem :
          encode_halt (B.compile c) ∈
            S1Rel W.Provable K Machine encode_halt
              (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
                (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)) :=
        mem_S1Rel_of_witness (Provable := W.Provable)
          (K := K) (Machine := Machine) (encode_halt := encode_halt)
          _ (B.compile c) hRev' hNprov'
      have : False := by
        simpa [hEmptyCollatz] using hMem
      exact this.elim

  -- 2) Use T2 on Universal to derive False
  let S_PA : ImpossibleSystem PropT := {
    Provable := W.SProvable_PA
    FalseT := (0 : Nat)
    Not := W.SNot_PA
    consistent := B.S_PA_consistent
    absurd := B.S_PA_absurd
  }

  let Γ_omega := omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
    (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)
  have hSound_omega : Soundness W.Provable S_PA.Provable Γ_omega := B.hSound_U Γ_omega

  -- Apply T2 (classical)
  apply frontier_empty_T2_full (Provable := W.Provable) (K := K) (encode_halt := B.encode_U)
    S_PA
    (DetectsUpFixed_StandardKit)
    hEmptyUniversal
    hSound_omega
    B.hNegComp_U
    B.hTotal_U
    B.f_U B.hf_U B.hsemidec_U

-- =============================================================================
-- Dynamic bridge (optional fallback, no universal compile)
-- =============================================================================

theorem bridge_proof_dynamic
    (W : CollatzWitnessesData)
    (hSound :
      ∀ t : Nat,
        Soundness W.Provable W.SProvable_PA
          (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
            (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)))
    (hNegComp : NegativeComplete K Machine encode_halt W.SProvable_PA W.SNot_PA)
    (hBarrier :
      (∀ e : Code, W.SProvable_PA (encode_halt e) ∨ W.SProvable_PA (W.SNot_PA (encode_halt e))) → False) :
    PA_implies_RouteIIAt
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := W.Cn) (A0 := W.A0) (hIdem := W.hIdem) (hProvCn := W.hProvCn) W.PAax := by
  intro t _hPA
  have hNonempty :
      (S1Rel W.Provable K Machine encode_halt
        (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
          (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t))).Nonempty := by
    apply frontier_nonempty_of_route_II
      (Provable := W.Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (SProvable := W.SProvable_PA) (SNot := W.SNot_PA)
    · exact hSound t
    · exact hNegComp
    · exact hBarrier
  simpa [RouteIIAt] using hNonempty

end RevHalt.Instances
