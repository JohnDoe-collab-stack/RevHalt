import RevHalt.Base
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Impossibility
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.UnifiedArchitecture

## A Single Interdependent Structure

This file formalizes the unified architecture where:
- **Machine is the primitive**: `Machine : Code → Trace` is fixed (not parameterized)
- **LR is derived**: `LR Γ φ := Machine (compile Γ φ)`
- **Kit is a parameter**: not wrapped in a structure

The architecture is **interdependent**: the bridge goes through Machine,
and all components reference the same primitive.

## Structure

1. Machine (fixed primitive)
2. Semantics (Sat, CloE, evaluation)
3. Compilation (compile : sentences → Code)
4. LR (derived from Machine + compile)
5. Bridge (on Machine, not LR)
6. Master theorem (E ↔ Halts(Machine) ↔ Rev0_K)
-/

namespace RevHalt

open Nat.Partrec

/-!
## 1) Machine: The Fixed Primitive

Machine is not parameterized. It is THE canonical interpreter.
-/

-- Machine is already defined in RevHalt.Base as:
-- def Machine (c : Code) : Trace := fun _ => ∃ x, x ∈ c.eval 0

-- Code is Nat.Partrec.Code (from Mathlib)

/-!
## 2) Compilation: Sentences to Code

The key structural component: compile sentences to Machine code.
-/

/-- A compilation function from semantic queries to Machine code.
    Note: Sentence only, no Model parameter needed. -/
abbrev Compile (Sentence : Type) : Type :=
  Set Sentence → Sentence → Code

/-- LR is DERIVED from Machine and compile: LR Γ φ := Machine (compile Γ φ) -/
abbrev LR_from_compile {Sentence : Type} (compile : Compile Sentence) :
    Set Sentence → Sentence → Trace :=
  fun Γ φ => Machine (compile Γ φ)

/-- Simp lemma for unfolding LR_from_compile. -/
@[simp] lemma LR_from_compile_apply {Sentence : Type} (compile : Compile Sentence)
    (Γ : Set Sentence) (φ : Sentence) :
    LR_from_compile compile Γ φ = Machine (compile Γ φ) := rfl

/-!
## 3) Bridge: On Machine (Not LR)

The bridge is fundamentally about Machine, not LR.
LR-based bridge is a corollary.
-/

section Bridge

variable {Sentence Model : Type}

/-- The fundamental bridge: semantic evaluation ↔ Machine halting.
    This is the primitive form. -/
def DynamicBridgeMachine
    (Sat : Model → Sentence → Prop)
    (compile : Compile Sentence) : Prop :=
  ∀ Γ φ, SemConsequences Sat Γ φ ↔ Halts (Machine (compile Γ φ))

/-- From DynamicBridgeMachine to DynamicBridge on derived LR. -/
theorem DynamicBridgeMachine.toDynamicBridge
    (Sat : Model → Sentence → Prop)
    (compile : Compile Sentence)
    (h : DynamicBridgeMachine Sat compile) :
    DynamicBridge Sat (LR_from_compile compile) := by
  intro Γ φ
  simpa [LR_from_compile] using (h Γ φ)

end Bridge

/-!
## 4) T1 Applied to Machine Traces

T1 (canonicity) applies directly to Machine traces.
Kit is a PARAMETER, not wrapped.
-/

section T1_on_Machine

/-- T1 specialized to Machine traces:
    For any valid Kit K and any code e,
    Rev0_K K (Machine e) ↔ Halts (Machine e) -/
theorem T1_on_Machine (K : RHKit) (hK : DetectsMonotone K) (e : Code) :
    Rev0_K K (Machine e) ↔ Halts (Machine e) :=
  T1_traces K hK (Machine e)

/-- All valid Kits agree on Machine traces. -/
theorem kits_agree_on_Machine (K1 K2 : RHKit)
    (h1 : DetectsMonotone K1) (h2 : DetectsMonotone K2) (e : Code) :
    Rev0_K K1 (Machine e) ↔ Rev0_K K2 (Machine e) :=
  T1_uniqueness K1 K2 h1 h2 (Machine e)

end T1_on_Machine

/-!
## 5) The Unified Architecture

One single structure with interdependent components.
-/

variable {Sentence Model : Type}

/-- The unified RevHalt architecture.
    Machine is fixed. LR is derived. All components are interdependent. -/
structure UnifiedArchitecture (Sentence Model : Type) where
  /-- Semantic satisfaction relation -/
  Sat : Model → Sentence → Prop
  /-- Compilation to Machine code -/
  compile : Compile Sentence
  /-- The fundamental bridge (on Machine) -/
  bridge : DynamicBridgeMachine Sat compile

/-- LR derived from the architecture. -/
def UnifiedArchitecture.LR (A : UnifiedArchitecture Sentence Model) :
    Set Sentence → Sentence → Trace :=
  LR_from_compile A.compile

/-- Simp lemma for UnifiedArchitecture.LR. -/
@[simp] lemma UnifiedArchitecture.LR_apply (A : UnifiedArchitecture Sentence Model)
    (Γ : Set Sentence) (φ : Sentence) :
    A.LR Γ φ = Machine (A.compile Γ φ) := by rfl

/-- Evaluation derived from the architecture. -/
def UnifiedArchitecture.Eval (A : UnifiedArchitecture Sentence Model)
    (Γ : Set Sentence) (φ : Sentence) : Prop :=
  SemConsequences A.Sat Γ φ

/-- Simp lemma for UnifiedArchitecture.Eval. -/
@[simp] lemma UnifiedArchitecture.Eval_def (A : UnifiedArchitecture Sentence Model)
    (Γ : Set Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ SemConsequences A.Sat Γ φ := Iff.rfl

/-- API Lemma: Evaluation ↔ Halts(Machine(compile)).
    This direct bridge is useful for proofs. -/
theorem eval_iff_halts
    (A : UnifiedArchitecture Sentence Model)
    (Γ : Set Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ Halts (Machine (A.compile Γ φ)) := by
  simpa [UnifiedArchitecture.Eval] using (A.bridge Γ φ)

/-!
## 6) Coverage: Local/Global Preparation

CoversMachine formalizes when compilation "covers" all Machine codes.
-/

/-- Coverage property: every Machine code is reachable via compile. -/
def CoversMachine {Sentence : Type} (compile : Compile Sentence) : Prop :=
  ∀ e : Code, ∃ (Γ : Set Sentence) (φ : Sentence), compile Γ φ = e

/-- If CoversMachine holds, each code e has a witness (Γ, φ) with the bridge equivalence. -/
theorem coverage_gives_instance_bridge
    {Sentence Model : Type}
    (A : UnifiedArchitecture Sentence Model)
    (hCover : CoversMachine A.compile)
    (e : Code) :
    ∃ (Γ : Set Sentence) (φ : Sentence),
      A.compile Γ φ = e ∧ (A.Eval Γ φ ↔ Halts (Machine e)) := by
  rcases hCover e with ⟨Γ, φ, hEq⟩
  refine ⟨Γ, φ, hEq, ?_⟩
  simpa [UnifiedArchitecture.Eval, hEq] using (A.bridge Γ φ)

/-- If CoversMachine and Eval is decidable for all (Γ, φ),
    then Halts(Machine e) is decidable for all e.
    This is the key transfer: global uniform decidability of Eval ⇒ global uniform decidability of Halts. -/
noncomputable def decidable_halts_of_decidable_eval
    {Sentence Model : Type}
    (A : UnifiedArchitecture Sentence Model)
    (hCover : CoversMachine A.compile)
    (hDec : ∀ (Γ : Set Sentence) (φ : Sentence), Decidable (A.Eval Γ φ))
    (e : Code) : Decidable (Halts (Machine e)) := by
  let Γ := Classical.choose (hCover e)
  let h1 := Classical.choose_spec (hCover e)
  let φ := Classical.choose h1
  have hEq : A.compile Γ φ = e := Classical.choose_spec h1
  have h : A.Eval Γ φ ↔ Halts (Machine e) := by
    simpa [UnifiedArchitecture.Eval, hEq] using (A.bridge Γ φ)
  cases hDec Γ φ with
  | isTrue hEval => exact isTrue (h.mp hEval)
  | isFalse hNotEval =>
      exact isFalse (by intro hH; exact hNotEval (h.mpr hH))

/-!
## 7) The Master Theorem

The central result: the full equivalence chain going through Machine.
-/

/-- **API Lemma**: Evaluation ↔ Rev0_K verdict (the main interface).
    This is the clean form to use in applications. -/
theorem eval_iff_rev
    (A : UnifiedArchitecture Sentence Model)
    (K : RHKit) (hK : DetectsMonotone K)
    (Γ : Set Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ Rev0_K K (Machine (A.compile Γ φ)) := by
  have h_bridge := eval_iff_halts A Γ φ
  have h_T1 : Rev0_K K (Machine (A.compile Γ φ)) ↔ Halts (Machine (A.compile Γ φ)) :=
    T1_traces K hK (Machine (A.compile Γ φ))
  exact h_bridge.trans h_T1.symm

/-- **Master Theorem (Bundle)**: The full equivalence chain (for documentation).
    Prefer `eval_iff_rev` for applications. -/
theorem master_theorem
    (A : UnifiedArchitecture Sentence Model)
    (K : RHKit) (hK : DetectsMonotone K)
    (Γ : Set Sentence) (φ : Sentence) :
    -- Step 1: Evaluation ↔ Machine halts
    (A.Eval Γ φ ↔ Halts (Machine (A.compile Γ φ))) ∧
    -- Step 2: Machine halts ↔ Rev0_K verdict
    (Halts (Machine (A.compile Γ φ)) ↔ Rev0_K K (Machine (A.compile Γ φ))) ∧
    -- Composition: Evaluation ↔ Rev0_K verdict
    (A.Eval Γ φ ↔ Rev0_K K (Machine (A.compile Γ φ))) := by
  have h_bridge := A.bridge Γ φ
  have h_T1 := T1_on_Machine K hK (A.compile Γ φ)
  exact ⟨h_bridge, h_T1.symm, eval_iff_rev A K hK Γ φ⟩

/-- All valid Kits give the same verdict (via the architecture). -/
theorem architecture_kit_invariance
    (A : UnifiedArchitecture Sentence Model)
    (K1 K2 : RHKit) (h1 : DetectsMonotone K1) (h2 : DetectsMonotone K2)
    (Γ : Set Sentence) (φ : Sentence) :
    Rev0_K K1 (Machine (A.compile Γ φ)) ↔ Rev0_K K2 (Machine (A.compile Γ φ)) :=
  kits_agree_on_Machine K1 K2 h1 h2 (A.compile Γ φ)

/-
## Summary

The architecture is:

```
Sat : Model → Sentence → Prop     (semantics)
compile : Set Sentence → Sentence → Code  (compilation)
                    │
                    ▼
              Machine (compile Γ φ)    (THE primitive)
                    │
       ┌────────────┼────────────┐
       ▼            ▼            ▼
    Halts    ←T1→  Rev0_K K  ←T1→  Halts
       │
       └── E(Γ,φ) via bridge
```

- Machine is fixed, not parameterized
- LR = Machine ∘ compile (derived)
- Bridge is on Machine (fundamental)
- T1 applies to Machine traces
- Kit K is a parameter, not packaged

This is a single interdependent structure, not 3 independent blocks.
-/

end RevHalt
