import RevHalt.Theory.RelativeFoundations
import RevHalt.Theory.RelativeR1

/-!
# Evaluative Trace Properties

This file formalizes the Evaluative Trace properties. It bridges the abstract LPO_R1 theory with the concrete semantics of HaltsE (Evaluative Halting) and StabilizesE (Evaluative Stabilization).

## 1. Abstract Trace Definitions

We begin by defining what it means for a sequence to Halt or Stabilize evaluatively. Note that StabilizesE is the constructive negation of HaltsE (it is not merely "failure to halt" in a weak sense, but a positive assertion of eternal stability).
-/

namespace RevHalt.TraceProperties

variable {Sentence : Type}

/-- HaltsE: the evaluation returns true at some index n. -/
def HaltsE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (s : ℕ → Sentence) : Prop :=
  ∃ n, Eval Γ (s n)

/-- StabilizesE: the evaluation remains false forever. -/
def StabilizesE (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (s : ℕ → Sentence) : Prop :=
  ∀ n, ¬ Eval Γ (s n)

/-- Theorem: HaltsE and StabilizesE are disjoint. -/
theorem HaltsE_and_StabilizesE_disjoint
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (s : ℕ → Sentence) :
    ¬ (HaltsE Eval Γ s ∧ StabilizesE Eval Γ s) := by
  intro h
  cases h with
  | intro hh hs =>
    cases hh with
    | intro n hn =>
      have hnot := hs n
      exact hnot hn

/-!
## 2. The LPO Connection (Dichotomy)

This section proves that LPO_R1 is exactly the assertion that every admissible trace must either evaluatively halt or evaluatively stabilize. This establishes the hierarchy: if the grammar Adm is too rich (e.g., all sequences), this principle becomes EM. If Adm is restricted (e.g., AdmBit), this principle is constructively weaker.
-/

theorem LPO_R1_iff_Trace_Dichotomy
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) :
    RevHalt.RelativeR1.LPO_Eval_R1 Eval Γ Adm ↔
    (∀ s, Adm s → HaltsE Eval Γ s ∨ StabilizesE Eval Γ s) := by
  rfl

/-!
## 3. Bit-Specific Trace Properties

Here we specialize the trace properties to the Bit Grammar (AdmBit). This is where the digital physics intuition connects to the logic: a "Halt" on a Bit sequence corresponds to finding a specific bit-value that satisfies the evaluation predicate (a "witness").
We use AdmBit from the previous file.
-/

namespace BitTraces

variable {Referent : Type}

theorem Bit_HaltsE_Witness
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence)
    (x : Referent) (s : ℕ → Sentence) :
    RevHalt.RelativeR1.CutBit.AdmBit Bit x s →
    HaltsE Eval Γ s →
    ∃ (n : ℕ) (a : Fin 2), s n = Bit n a x ∧ Eval Γ (Bit n a x) := by
  intro hAdm hHalt
  cases hHalt with
  | intro n hEval =>
    have hSn := hAdm n
    cases hSn with
    | intro a hEq =>
      exists n
      exists a
      constructor
      exact hEq
      rw [←hEq]
      exact hEval

theorem Bit_StabilizesE_AllFalse
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence)
    (x : Referent) (s : ℕ → Sentence) :
    RevHalt.RelativeR1.CutBit.AdmBit Bit x s →
    StabilizesE Eval Γ s →
    ∀ n, ∀ a, s n = Bit n a x → ¬ Eval Γ (Bit n a x) := by
  intro _ hStab n a hEq
  have hNot := hStab n
  rw [hEq] at hNot
  exact hNot

end BitTraces
end RevHalt.TraceProperties
