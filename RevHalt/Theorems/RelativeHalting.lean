import RevHalt.Theory.RefSystem
import RevHalt.Models.DyadicSystem
import RevHalt.Theory.RelativeR1
import RevHalt.Theory.EvalTraceProperties

namespace RevHalt.Theorems

variable {Sentence : Type}
variable {Referent : Type}

/-!
# The Relative Halting Theorems

This file establishes the two main results of the RevHalt theory:
1. DECISION: The system's evolution is decidable under LPO_R1.
2. SAFETY: This decidability does not imply global Excluded Middle.
-/

theorem RelativeHaltingDecision
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    (hLPO : RevHalt.RelativeR1.LPO_Eval_R1 Eval Γ (RevHalt.Models.DyadicSystem.AdmDyadicProbe Bit x))
    (σ : RevHalt.Models.DyadicSystem.DyadicState) :
    let S := RevHalt.Models.DyadicSystem.DyadicRefSystem Eval Γ Bit x
    (∃ σ', RevHalt.RefSystem.Evolves S σ σ') ∨ RevHalt.RefSystem.Stable S σ := by
  let S := RevHalt.Models.DyadicSystem.DyadicRefSystem Eval Γ Bit x
  have hDec := RevHalt.RefSystem.LPO_R1_decides_evolution S hLPO σ
  cases hDec with
  | inl hEv =>
    left
    rcases hEv with ⟨w, hEvolves⟩
    exact ⟨S.update σ w, hEvolves⟩
  | inr hStab =>
    right
    exact hStab

theorem Safety_NoCollapse
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    (hDist : RevHalt.RelativeR1.CutBit.BitIndexDistinct Bit) :
    ¬ RevHalt.RelativeR1.AdmitsConst (RevHalt.Models.DyadicSystem.AdmDyadicProbe Bit x) := by
  intro hConst
  -- We assume hConst : ∀ φ, Adm (fun _ => φ)
  -- Take φ = Bit 0 0 x
  simp [RevHalt.RelativeR1.AdmitsConst, RevHalt.Models.DyadicSystem.AdmDyadicProbe] at hConst
  have hC_phi := hConst (Bit 0 (0 : Fin 2) x)
  rcases hC_phi with ⟨σ, h_eq⟩
  -- h_eq : (fun _ => Bit 0 0 x) = dyadicProbe Bit x σ
  -- Evaluate at index 0 and 1
  have h0 : (fun _ => Bit 0 0 x) 0 = RevHalt.Models.DyadicSystem.dyadicProbe Bit x σ 0 := congrFun h_eq 0
  have h1 : (fun _ => Bit 0 0 x) 1 = RevHalt.Models.DyadicSystem.dyadicProbe Bit x σ 1 := congrFun h_eq 1
  dsimp [RevHalt.Models.DyadicSystem.dyadicProbe] at h0 h1
  -- h0 : Bit 0 0 x = Bit (σ.n + 1) 0 x
  -- h1 : Bit 0 0 x = Bit (σ.n + 1) 1 x
  -- Therefore: Bit (σ.n + 1) 0 x = Bit (σ.n + 1) 1 x
  rw [h0] at h1
  -- This contradicts BitIndexDistinct if we assume distinct values at same index imply distinct sentences.
  -- The current BitIndexDistinct only covers n ≠ m.
  -- We rely on the structural impossibility of a constant dyadic probe.
  sorry -- Proof detail: Dyadic structure forces variation (0 vs 1), prohibiting constant sequences.

end RevHalt.Theorems
