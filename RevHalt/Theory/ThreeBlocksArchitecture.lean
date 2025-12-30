import RevHalt.Base
import RevHalt.Theory.Canonicity
import RevHalt.Theory.Impossibility
import RevHalt.Theory.Complementarity
import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.OracleMachine

## Oracle Machine Architecture (a-machine / o-machine / c-machine)

This file formalizes the architecture following the standard distinction:
- **a-machine** (Automatic/Mechanical): The primitive `Machine` (UTM).
- **o-machine** (Oracle): The bridge `OracleBridge` connecting semantics to mechanics.
- **c-machine** (Choice): The external compilation process (`List Sentence → Code`).

## Oracle Localization

> [!IMPORTANT]
> The ONLY place where non-mechanical power enters is the `OracleBridge` (specifically `Sat`).
> - `aMachine` is purely mechanical (PartRec).
> - `compile` is a translation/choice function (c-machine).
> - `Sat` provides the oracle power via the bridge.

This structure allows us to separate:
1. **T1 (Canonicity)**: Properties of the a-machine traces.
2. **Architecture**: Connection between o-machine (Eval) and a-machine (Halts).
3. **T2 (Impossibility)**: What cannot be internalized.
-/

namespace RevHalt

open Nat.Partrec

/-!
## 1) a-machine: The Mechanical Primitive
-/

/-- The a-machine (UTM). Fixed, purely mechanical. -/
abbrev aMachine := Machine

/-- Notion of Convergence (Halting) for the a-machine. -/
def Converges (e : Code) : Prop := ∃ x, x ∈ e.eval 0

/-- API Lemma: Halts(aMachine) is exactly Convergence. -/
theorem halts_aMachine_iff (e : Code) :
    Halts (aMachine e) ↔ Converges e := by
  dsimp [Halts, aMachine, Converges]
  -- We assume Machine is defined as const trace of convergence in Base
  -- If not unfolded, use basic logic on 'exists'
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; use 0; exact h

/-!
## 2) c-machine: Compilation
-/

/-- The c-machine translation logic.
    Uses `List Sentence` (effective) instead of `Set Sentence`. -/
abbrev Compile (Sentence : Type) : Type :=
  List Sentence → Sentence → Code

/-- Helper: convert List Sentence to Set Sentence. -/
def Γset {Sentence} (Γ : List Sentence) : Set Sentence := { s | s ∈ Γ }

/-- LR is DERIVED: LR Γ φ := aMachine (compile Γ φ). -/
def LR_from_compile {Sentence : Type} (compile : Compile Sentence) :
    List Sentence → Sentence → Trace :=
  fun Γ φ => aMachine (compile Γ φ)

@[simp] lemma LR_from_compile_apply {Sentence : Type} (compile : Compile Sentence)
    (Γ : List Sentence) (φ : Sentence) :
    LR_from_compile compile Γ φ = aMachine (compile Γ φ) := rfl

/-!
## 3) o-machine: The Oracle Bridge
-/

section Bridge

variable {Sentence Model : Type}

/-- The Oracle Bridge (o-bridge).
    Connects semantic truth (Oracle) to mechanical convergence (a-machine).
    Uses `Γset` to convert List to Set. -/
def OracleBridge
    (Sat : Model → Sentence → Prop)
    (compile : Compile Sentence) : Prop :=
  ∀ (Γ : List Sentence) (φ : Sentence),
    SemConsequences Sat (Γset Γ) φ ↔ Converges (compile Γ φ)



end Bridge

/-!
## 4) T1 on a-machine
-/

section T1_on_aMachine

theorem T1_on_aMachine (K : RHKit) (hK : DetectsMonotone K) (e : Code) :
    Rev0_K K (aMachine e) ↔ Halts (aMachine e) :=
  T1_traces K hK (aMachine e)

theorem kits_agree_on_aMachine (K1 K2 : RHKit)
    (h1 : DetectsMonotone K1) (h2 : DetectsMonotone K2) (e : Code) :
    Rev0_K K1 (aMachine e) ↔ Rev0_K K2 (aMachine e) :=
  T1_uniqueness K1 K2 h1 h2 (aMachine e)

end T1_on_aMachine

/-!
## 5) OracleMachine Structure
-/

variable {Sentence Model : Type}

/-- The Oracle Machine (Architecture).
    Encapsulates the a-machine, c-machine choice, and o-machine bridge. -/
structure OracleMachine (Sentence Model : Type) where
  /-- Semantic Oracle (Sat) -/
  Sat : Model → Sentence → Prop
  /-- c-machine (Compiler) from List Sentence -/
  compile : Compile Sentence
  /-- o-bridge (Connection) -/
  oBridge : OracleBridge Sat compile

/-- LR derived from the OracleMachine. -/
def OracleMachine.LR (A : OracleMachine Sentence Model) :
    List Sentence → Sentence → Trace :=
  LR_from_compile A.compile

/-- Explicit Def: LR is aMachine run on compiled code. -/
@[simp] lemma OracleMachine.LR_def (A : OracleMachine Sentence Model)
    (Γ : List Sentence) (φ : Sentence) :
    A.LR Γ φ = aMachine (A.compile Γ φ) := rfl

/-- o-machine evaluation (Semantics). -/
def OracleMachine.Eval (A : OracleMachine Sentence Model)
    (Γ : List Sentence) (φ : Sentence) : Prop :=
  SemConsequences A.Sat (Γset Γ) φ

@[simp] lemma OracleMachine.Eval_def (A : OracleMachine Sentence Model)
    (Γ : List Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ SemConsequences A.Sat (Γset Γ) φ := Iff.rfl

/-- API Lemma: Eval ↔ Halts(aMachine). -/
theorem eval_iff_halts
    (A : OracleMachine Sentence Model)
    (Γ : List Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ Halts (aMachine (A.compile Γ φ)) := by
  rw [halts_aMachine_iff]
  exact A.oBridge Γ φ

/-!
## 6) Properties: Coverage & Decidability
-/

/-- CompiledWitness: A constructive witness for code coverage. -/
structure CompiledWitness {Sentence : Type} (compile : Compile Sentence) (e : Code) where
  Γ : List Sentence
  φ : Sentence
  hEq : compile Γ φ = e

/-- CompileCover: Canonical constructive coverage. -/
def CompileCover {Sentence : Type} (compile : Compile Sentence) : Type :=
  ∀ e : Code, CompiledWitness compile e

/-- Transfer: Decidable Eval + Covered Compilation ⇒ Decidable Halts. -/
def decidable_halts_of_decidable_eval
    {Sentence Model : Type}
    (A : OracleMachine Sentence Model)
    (hCover : CompileCover A.compile)
    (hDec : ∀ (Γ : List Sentence) (φ : Sentence), Decidable (A.Eval Γ φ))
    (e : Code) : Decidable (Halts (aMachine e)) := by
  rcases hCover e with ⟨Γ, φ, hEq⟩
  have hBridge : A.Eval Γ φ ↔ Halts (aMachine (A.compile Γ φ)) :=
    eval_iff_halts A Γ φ
  rw [hEq] at hBridge
  cases hDec Γ φ with
  | isTrue hEval => exact isTrue (hBridge.mp hEval)
  | isFalse hNotEval =>
      exact isFalse (fun hH => hNotEval (hBridge.mpr hH))

/-!
## 7) The Master Theorem
-/

theorem eval_iff_rev
    (A : OracleMachine Sentence Model)
    (K : RHKit) (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence) :
    A.Eval Γ φ ↔ Rev0_K K (aMachine (A.compile Γ φ)) := by
  have h_bridge := eval_iff_halts A Γ φ
  have h_T1 : Rev0_K K (aMachine (A.compile Γ φ)) ↔ Halts (aMachine (A.compile Γ φ)) :=
    T1_traces K hK (aMachine (A.compile Γ φ))
  exact h_bridge.trans h_T1.symm

/-!
## 8) Architectural Constraints & T2 Barrier
-/

section ArchitecturalConstraints

variable {Sentence Model PropT : Type}
variable (A : OracleMachine Sentence Model)
variable (S : ImpossibleSystem PropT)
variable (K : RHKit)

/-- 1) From Architecture to External Decider for Rev0. -/
def decidable_rev0_of_decidable_eval
    (hK : DetectsMonotone K)
    (hCover : CompileCover A.compile)
    (hDec : ∀ (Γ : List Sentence) (φ : Sentence), Decidable (A.Eval Γ φ))
    (e : Code) : Decidable (Rev0_K K (aMachine e)) := by
  -- 1. Decidable Halts
  have dH : Decidable (Halts (aMachine e)) :=
    decidable_halts_of_decidable_eval A hCover hDec e
  -- 2. Transport via T1
  have hT1 : Rev0_K K (aMachine e) ↔ Halts (aMachine e) :=
    T1_traces K hK (aMachine e)

  cases dH with
  | isTrue hH => exact isTrue (hT1.mpr hH)
  | isFalse hH => exact isFalse (fun hR => hH (hT1.mp hR))

/-- 2) The Internalization Axiom (The Barrier).
    Hypothesis asserting that any external decider can be lifted to an internal halting predicate. -/
def InternalizeDecider : Prop :=
  (∀ _ : (∀ e : Code, Decidable (Rev0_K K (aMachine e))),
     ∃ _ : InternalHaltingPredicate (PropT := PropT) S K, True)

/-- 3) The Contradiction (Complementarity). -/
theorem contradiction_if_internalize_external_decider
    (hK : DetectsMonotone K)
    (hCover : CompileCover A.compile)
    (hDec : ∀ (Γ : List Sentence) (φ : Sentence), Decidable (A.Eval Γ φ))
    (hLift : InternalizeDecider S K) :
    False := by
  have dRev : ∀ e : Code, Decidable (Rev0_K K (aMachine e)) :=
    fun e => decidable_rev0_of_decidable_eval A K hK hCover hDec e
  have hIH : ∃ IH : InternalHaltingPredicate S K, True :=
    hLift dRev
  exact T2_impossibility S K hK hIH

end ArchitecturalConstraints

/-!
## 9) T3 Integration — Certificate Types
-/

section Certificates

variable (K : RHKit)

/-- Σ₁ certificate: the machine halts. -/
def HaltCertificate (e : Code) : Prop := Rev0_K K (aMachine e)

/-- Π₁ certificate: the machine stabilizes. -/
def StabCertificate (e : Code) : Prop := KitStabilizes K (aMachine e)

/-- Σ₁ and Π₁ certificates are mutually exclusive (by definition). -/
theorem certificate_exclusion_aMachine (e : Code) :
    ¬ (HaltCertificate K e ∧ StabCertificate K e) := by
  intro ⟨hHalt, hStab⟩
  show False
  have hH : Rev0_K K (aMachine e) := hHalt
  have hS : ¬ Rev0_K K (aMachine e) := hStab
  exact hS hH

/-- HaltCertificate ↔ Halts for valid kit. -/
theorem haltCertificate_iff_halts (hK : DetectsMonotone K) (e : Code) :
    HaltCertificate K e ↔ Halts (aMachine e) := by
  unfold HaltCertificate
  exact T1_traces K hK (aMachine e)

/-- StabCertificate ↔ Stabilizes for valid kit. -/
theorem stabCertificate_iff_stabilizes (hK : DetectsMonotone K) (e : Code) :
    StabCertificate K e ↔ Stabilizes (aMachine e) := by
  unfold StabCertificate
  exact T1_stabilization K hK (aMachine e)

end Certificates

/-!
## 10) T3 Integration — Architecture to Certificates
-/

section ArchitecturalCertificates

variable {Sentence Model : Type}
variable (A : OracleMachine Sentence Model)
variable (K : RHKit)

/-- If Eval holds, the compiled code has a Σ₁ certificate. -/
theorem eval_gives_halt_certificate
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (hEval : A.Eval Γ φ) :
    HaltCertificate K (A.compile Γ φ) := by
  unfold HaltCertificate
  have h := eval_iff_rev A K hK Γ φ
  exact h.mp hEval

/-- If ¬Eval holds, the compiled code has a Π₁ certificate. -/
theorem not_eval_gives_stab_certificate
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (hNotEval : ¬ A.Eval Γ φ) :
    StabCertificate K (A.compile Γ φ) := by
  unfold StabCertificate KitStabilizes
  have h := eval_iff_rev A K hK Γ φ
  intro hRev
  exact hNotEval (h.mpr hRev)

/-- Σ₁ certificate ↔ Eval. -/
theorem haltCertificate_iff_eval
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence) :
    HaltCertificate K (A.compile Γ φ) ↔ A.Eval Γ φ := by
  unfold HaltCertificate
  exact (eval_iff_rev A K hK Γ φ).symm

/-- Π₁ certificate ↔ ¬Eval. -/
theorem stabCertificate_iff_not_eval
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence) :
    StabCertificate K (A.compile Γ φ) ↔ ¬ A.Eval Γ φ := by
  unfold StabCertificate KitStabilizes
  have h := eval_iff_rev A K hK Γ φ
  constructor
  · intro hStab hEval
    exact hStab (h.mp hEval)
  · intro hNotEval hRev
    exact hNotEval (h.mpr hRev)

end ArchitecturalCertificates

/-!
## 11) T3 Integration — OracleMachine to OraclePick

The key connection between the OracleMachine architecture and T3:

1. **c-machine** compiles `(Γ, φ)` to a `Code`
2. **o-bridge** guarantees `Eval Γ φ ↔ Converges (compile Γ φ)`
3. **Sections 9-10** give us: `Eval ↔ HaltCertificate`, `¬Eval ↔ StabCertificate`
4. **This section** packages this as an `ArchitecturalOraclePick`

The architectural pick is an OraclePick that comes from the OracleMachine structure,
where the certificate is derived from the o-bridge evaluation.
-/

section OracleMachineToT3

variable {Sentence Model : Type}
variable (A : OracleMachine Sentence Model)
variable (K : RHKit)

/--
  An architectural oracle pick for a compiled code.

  Given `Γ : List Sentence` and `φ : Sentence`:
  - The c-machine compiles them to `e := A.compile Γ φ`
  - The o-bridge gives us: `A.Eval Γ φ ↔ Converges e`
  - We package either:
    - `HaltCertificate K e` (Σ₁) if `A.Eval Γ φ`, or
    - `StabCertificate K e` (Π₁) if `¬ A.Eval Γ φ`
-/
structure ArchitecturalOraclePick (Γ : List Sentence) (φ : Sentence) where
  /-- The compiled code via c-machine -/
  code : Code := A.compile Γ φ
  /-- The certificate: either Σ₁ (halt) or Π₁ (stab) -/
  cert : HaltCertificate K code ∨ StabCertificate K code

/-- From a positive Eval, we get a Σ₁ certificate. -/
def architecturalPick_of_eval
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (hEval : A.Eval Γ φ) :
    ArchitecturalOraclePick A K Γ φ where
  code := A.compile Γ φ
  cert := Or.inl (eval_gives_halt_certificate A K hK Γ φ hEval)

/-- From a negative Eval, we get a Π₁ certificate. -/
def architecturalPick_of_not_eval
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (hNotEval : ¬ A.Eval Γ φ) :
    ArchitecturalOraclePick A K Γ φ where
  code := A.compile Γ φ
  cert := Or.inr (not_eval_gives_stab_certificate A K hK Γ φ hNotEval)

/-- The architectural pick is exhaustive: every compiled code has a certificate. -/
theorem architecturalPick_exhaustive
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (h : A.Eval Γ φ ∨ ¬ A.Eval Γ φ) :
    ∃ _ : ArchitecturalOraclePick A K Γ φ, True := by
  cases h with
  | inl hE => exact ⟨architecturalPick_of_eval A K hK Γ φ hE, trivial⟩
  | inr hNE => exact ⟨architecturalPick_of_not_eval A K hK Γ φ hNE, trivial⟩

/--
  **Architectural T3 Theorem**:

  Given an OracleMachine with:
  - a-machine: `aMachine`
  - c-machine: `A.compile`
  - o-bridge: `A.oBridge`

  And an `ArchitecturalOraclePick` for `(Γ, φ)`:

  The o-bridge + T1 gives us a certificate (Σ₁ or Π₁) for the compiled code,
  which can be used to construct sound extensions in T3.
-/
theorem architectural_T3_certificate_transfer
    (hK : DetectsMonotone K)
    (Γ : List Sentence) (φ : Sentence)
    (pick : ArchitecturalOraclePick A K Γ φ) :
    (Halts (aMachine pick.code) ∧ HaltCertificate K pick.code) ∨
    (Stabilizes (aMachine pick.code) ∧ StabCertificate K pick.code) := by
  cases pick.cert with
  | inl hHalt =>
      have hH : Halts (aMachine pick.code) := (haltCertificate_iff_halts K hK pick.code).mp hHalt
      exact Or.inl ⟨hH, hHalt⟩
  | inr hStab =>
      have hS : Stabilizes (aMachine pick.code) := (stabCertificate_iff_stabilizes K hK pick.code).mp hStab
      exact Or.inr ⟨hS, hStab⟩

end OracleMachineToT3

end RevHalt
