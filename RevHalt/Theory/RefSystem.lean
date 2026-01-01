import RevHalt.Theory.RelativeFoundations
import RevHalt.Theory.RelativeR1
import RevHalt.Theory.EvalTraceProperties

namespace RevHalt.RefSystem

variable {Sentence : Type}

structure TraceWitness (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (s : ℕ → Sentence) where
  n : ℕ
  h : Eval Γ (s n)

structure System (State : Type) (Adm : (ℕ → Sentence) → Prop)
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) where
  probe : State → (ℕ → Sentence)
  probe_adm : ∀ σ, Adm (probe σ)
  update : (σ : State) → TraceWitness Eval Γ (probe σ) → State

variable {State : Type}
variable {Adm : (ℕ → Sentence) → Prop}
variable {Eval : List Sentence → Sentence → Prop}
variable {Γ : List Sentence}

def Evolves (S : System State Adm Eval Γ) (σ σ' : State) : Prop :=
  ∃ w : TraceWitness Eval Γ (S.probe σ), S.update σ w = σ'

def Stable (S : System State Adm Eval Γ) (σ : State) : Prop :=
  RevHalt.TraceProperties.StabilizesE Eval Γ (S.probe σ)

theorem Evolves_imp_HaltsE (S : System State Adm Eval Γ) (σ σ' : State) :
    Evolves S σ σ' → RevHalt.TraceProperties.HaltsE Eval Γ (S.probe σ) := by
  intro h
  cases h with
  | intro w _ =>
    exists w.n
    exact w.h

theorem Stable_imp_not_Evolves (S : System State Adm Eval Γ) (σ : State) :
    Stable S σ → ∀ σ', ¬ Evolves S σ σ' := by
  intro hStab σ' hEv
  have hHalt := Evolves_imp_HaltsE S σ σ' hEv
  exact RevHalt.TraceProperties.HaltsE_and_StabilizesE_disjoint Eval Γ (S.probe σ) ⟨hHalt, hStab⟩

theorem LPO_R1_decides_evolution
    (S : System State Adm Eval Γ)
    (hLPO : RevHalt.RelativeR1.LPO_Eval_R1 Eval Γ Adm)
    (σ : State) :
    (∃ w, Evolves S σ (S.update σ w)) ∨ Stable S σ := by
  have hAdm := S.probe_adm σ
  have hDich := hLPO (S.probe σ) hAdm
  cases hDich with
  | inl hHalt =>
    left
    cases hHalt with
    | intro n hEval =>
      let w : TraceWitness Eval Γ (S.probe σ) := ⟨n, hEval⟩
      exists w
      exists w
  | inr hStab =>
    right
    exact hStab

end RevHalt.RefSystem
