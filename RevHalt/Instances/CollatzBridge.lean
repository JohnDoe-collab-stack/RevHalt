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

def CollatzBridgeAssumptions_of_AssumptionsD
    (A : CollatzWitnessesAssumptionsD)
    (encode_U : UCode → PropT)
    (compile : UCode → Code)
    (hEncode : ∀ c, encode_U c = encode_halt (compile c))
    (hSim :
      ∀ c, Rev0_K K (UMachine c) →
        Rev0_K K (Machine (compile c)))
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
    richness_bridge_axiom := by
      intro Γ hEmpty
      -- Show emptiness of U frontier from Collatz frontier emptiness.
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      obtain ⟨c, hpEq, hRev, hNprov⟩ := hp
      have hRev' : Rev0_K K (Machine (compile c)) := hSim c hRev
      have hNprov' : ¬ (CollatzWitnessesData_of_AssumptionsD A).Provable Γ
          (encode_halt (compile c)) := by
        simpa [hEncode c] using hNprov
      have hMem :
          encode_halt (compile c) ∈
            S1Rel (CollatzWitnessesData_of_AssumptionsD A).Provable K Machine encode_halt Γ :=
        mem_S1Rel_of_witness (Provable := (CollatzWitnessesData_of_AssumptionsD A).Provable)
          (K := K) (Machine := Machine) (encode_halt := encode_halt)
          Γ (compile c) hRev' hNprov'
      -- Contradiction with emptiness
      have : False := by
        simpa [hEmpty] using hMem
      exact this.elim
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

  -- 1) Use Bridge to switch to Universal
  have hEmptyUniversal :
      S1Rel W.Provable K UMachine B.encode_U
        (omegaΓ W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn
          (chainState W.Provable K Machine encode_halt W.Cn W.hIdem W.hProvCn W.A0 t)) = ∅ :=
    B.richness_bridge_axiom hEmptyCollatz

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
    (hSound : ∀ Γ, Soundness W.Provable W.SProvable_PA Γ)
    (hNegComp : NegativeComplete K Machine encode_halt W.SProvable_PA W.SNot_PA)
    (hDec : ∀ e, Decidable (W.SProvable_PA (encode_halt e)))
    (hBarrier : (∀ e, Decidable (W.SProvable_PA (encode_halt e))) → False) :
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
    · exact hSound _
    · exact hNegComp
    · exact hDec
    · exact hBarrier
  simpa [RouteIIAt] using hNonempty

-- 5) Trivial compile helper (constructive, not universal)
def compile_trivial : UCode → Code := fun _ => 1

def encode_U_trivial : UCode → PropT := fun _ => encode_halt 1

lemma encode_U_trivial_eq (c : UCode) :
    encode_U_trivial c = encode_halt (compile_trivial c) := by
  rfl

lemma sim_trivial : ∀ c, Rev0_K K (UMachine c) → Rev0_K K (Machine (compile_trivial c)) := by
  intro _ _
  -- Collatz halts on 1, hence Rev0_K is true.
  have hHalts : Halts (Machine 1) := by
    refine ⟨1, ?_⟩
    refine ⟨0, Nat.zero_lt_succ 0, ?_⟩
    simp [Machine, CollatzStep]
  exact (revK_iff_halts K DetectsUpFixed_StandardKit (Machine 1)).2 hHalts

end RevHalt.Instances
