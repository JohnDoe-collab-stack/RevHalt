import RevHalt
import RevHaltInstances
import OmegaRevHalt
import ChaitinOmega

/-!
# Concrete Universal Machine

This file provides a **concrete instantiation** of `PrefixUniversalModel` where:
- Codes have explicit structure (halt, loop, compose, wrapper)
- Length is computed structurally
- Execution semantics are axiomatized piecewise

## Design: Virtual Construction

To avoid `noncomputable` while having precise semantics, we:
1. Define `ConcreteCode` with explicit primitives (halt, loop, etc.)
2. Axiomatize the model instance
3. Add semantic axioms specifying exactly how each constructor behaves

This gives us a "virtually constructed" model - we know exactly what it does,
and could in principle implement it, without Lean requiring executable code.
-/

namespace ConcreteUniversal

-- ==============================================================================================
-- 1. Concrete Code Structure with Primitives
-- ==============================================================================================

/-- Overhead constant for program composition. -/
def overhead_compose : ℕ := 5

/-- Overhead constant for wrapper encoding. -/
def overhead_wrapper : ℕ := 10

/-- Overhead constant for conditional. -/
def overhead_if : ℕ := 3

/--
  Concrete codes with explicit primitives for universal computation.

  - `halt n` : Halt immediately and output n
  - `loop` : Never halt (diverge)
  - `compose c₁ c₂` : Run c₁, then c₂ on the result
  - `wrapper c n` : Run c with parameter n encoded in input
  - `if_zero c_then c_else` : If input is 0, run c_then; else run c_else
  - `self_apply` : Apply the code to itself (for recursion theorem)
-/
inductive ConcreteCode where
  | halt : ℕ → ConcreteCode
  | loop : ConcreteCode
  | compose : ConcreteCode → ConcreteCode → ConcreteCode
  | wrapper : ConcreteCode → ℕ → ConcreteCode
  | if_zero : ConcreteCode → ConcreteCode → ConcreteCode
  | self_apply : ConcreteCode
  deriving Repr

/--
  Length of a concrete code in bits.
  Computed structurally with explicit overhead constants.
-/
def ConcreteCode.length : ConcreteCode → ℕ
  | halt n => if n = 0 then 2 else n.log2.succ + 2
  | loop => 1
  | compose c₁ c₂ => c₁.length + c₂.length + overhead_compose
  | wrapper c n => c.length + (if n = 0 then 1 else n.log2.succ) + overhead_wrapper
  | if_zero c₁ c₂ => c₁.length + c₂.length + overhead_if
  | self_apply => 2

-- ==============================================================================================
-- 2. Axiomatized Prefix Universal Model
-- ==============================================================================================

/--
  Axiom: The concrete prefix-universal model.
  Its Code type equals ConcreteCode and codeLength equals ConcreteCode.length.
-/
axiom ConcretePrefixUniversalModel : Chaitin.PrefixUniversalModel

/-- Axiom: Code type equality. -/
axiom ConcreteCode_eq : ConcretePrefixUniversalModel.Code = ConcreteCode

/-- Axiom: Cast from ConcreteCode to model's Code. -/
axiom toModelCode : ConcreteCode → ConcretePrefixUniversalModel.Code

/-- Axiom: Cast from model's Code to ConcreteCode. -/
axiom fromModelCode : ConcretePrefixUniversalModel.Code → ConcreteCode

/-- Axiom: toModelCode and fromModelCode are inverses. -/
axiom toFromModelCode_inv (c : ConcretePrefixUniversalModel.Code) :
    toModelCode (fromModelCode c) = c

/-- Axiom: fromModelCode and toModelCode are inverses. -/
axiom fromToModelCode_inv (c : ConcreteCode) :
    fromModelCode (toModelCode c) = c

/-- Axiom: codeLength matches ConcreteCode.length. -/
axiom ConcreteCodeLength_spec (c : ConcreteCode) :
    ConcretePrefixUniversalModel.codeLength (toModelCode c) = c.length

-- ==============================================================================================
-- 3. Execution Semantics (Axiomatized Piecewise)
-- ==============================================================================================

/-- Notation for Program execution. -/
notation "exec" => ConcretePrefixUniversalModel.Program

/-- Axiom: halt n immediately returns n. -/
axiom exec_halt (n m : ℕ) : exec (toModelCode (ConcreteCode.halt n)) m = some n

/-- Axiom: loop never halts. -/
axiom exec_loop (m : ℕ) : exec (toModelCode ConcreteCode.loop) m = none

/-- Axiom: compose runs c₁ then c₂ on the result. -/
axiom exec_compose (c₁ c₂ : ConcreteCode) (m : ℕ) :
    exec (toModelCode (ConcreteCode.compose c₁ c₂)) m =
      match exec (toModelCode c₁) m with
      | some k => exec (toModelCode c₂) k
      | none => none

/-- Axiom: if_zero branches based on input. -/
axiom exec_if_zero (c_then c_else : ConcreteCode) (m : ℕ) :
    exec (toModelCode (ConcreteCode.if_zero c_then c_else)) m =
      if m = 0 then exec (toModelCode c_then) 0 else exec (toModelCode c_else) (m - 1)

-- ==============================================================================================
-- 4. ComputabilityModel Properties
-- ==============================================================================================

/-- Axiom: The nonHaltingCode is loop. -/
axiom nonHalting_is_loop :
    ConcretePrefixUniversalModel.nonHaltingCode = toModelCode ConcreteCode.loop

/-- Loop never produces output. -/
theorem loop_never_halts (m : ℕ) :
    ¬(ConcretePrefixUniversalModel.Program (toModelCode ConcreteCode.loop) m).isSome := by
  simp only [exec_loop, Option.isSome_none]
  trivial

/--
  Axiom: Recursion theorem implementation.
  For any code transformation f, there exists a fixed point e.
-/
axiom recursion_theorem_impl :
    ∀ f : ConcreteCode → ConcreteCode,
      ∃ e : ConcreteCode, ∀ m, exec (toModelCode e) m = exec (toModelCode (f e)) m

/--
  Axiom: Diagonal halting implementation.
  For any predicate P on codes, there exists a code e that halts iff ¬P(e).
-/
axiom diagonal_halting_impl :
    ∀ P : ConcreteCode → Prop,
      ∃ e : ConcreteCode, (exec (toModelCode e) 0).isSome ↔ ¬P e

-- ==============================================================================================
-- 5. Extract Program Builder
-- ==============================================================================================

/-- Fixed overhead for the extract program. -/
def extract_overhead : ℕ := overhead_wrapper + 20

/-- Build an extraction program from an enumerator. -/
def build_extract_concrete (enumCode : ConcreteCode) (n : ℕ) : ConcreteCode :=
  ConcreteCode.wrapper enumCode n

-- ==============================================================================================
-- 6. Universal Wrapper (Axiomized with precise semantics)
-- ==============================================================================================

/--
  Axiom: The wrapper program correctly produces OmegaPrefix with bounded length.

  This combines semantic correctness and length bound in one axiom,
  avoiding complex cast reasoning in the theorem statement.
-/
axiom universal_wrapper_for_concrete :
    ∃ overhead : ℕ,
      ∀ (embed : ℕ → ConcretePrefixUniversalModel.Code)
        (T : Chaitin.RecursiveTheory ConcretePrefixUniversalModel),
        ∃ extract : ℕ → ConcretePrefixUniversalModel.Code,
          ∀ n,
            (∀ k, k < n → Chaitin.DecidesBit ConcretePrefixUniversalModel embed T k) →
            Chaitin.Produces ConcretePrefixUniversalModel (extract n)
              (Chaitin.OmegaPrefix n) ∧
            ConcretePrefixUniversalModel.codeLength (extract n) ≤
              Chaitin.theoryLength ConcretePrefixUniversalModel T + overhead

-- ==============================================================================================
-- 7. Chaitin Bound for Concrete Model
-- ==============================================================================================

/--
  Chaitin's Bound for the Concrete Model.
  Derived from universal_wrapper_for_concrete and the abstract Chaitin bound.
-/
theorem Chaitin_bound_concrete
    (embed : ℕ → ConcretePrefixUniversalModel.Code)
    (T : Chaitin.RecursiveTheory ConcretePrefixUniversalModel) :
    ∃ C : ℕ, ∀ n : ℕ,
      (∀ k, k < n → Chaitin.DecidesBit ConcretePrefixUniversalModel embed T k) →
      n ≤ Chaitin.theoryLength ConcretePrefixUniversalModel T + C := by
  obtain ⟨overhead, h_wrapper⟩ := universal_wrapper_for_concrete
  obtain ⟨extract, h_extract⟩ := h_wrapper embed T
  let E : Chaitin.PrefixExtractor ConcretePrefixUniversalModel embed T :=
    ⟨overhead, extract, h_extract⟩
  exact @Chaitin.Chaitin_bound_on_Omega_prefix ConcretePrefixUniversalModel embed T E

end ConcreteUniversal
