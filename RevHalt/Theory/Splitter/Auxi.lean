import RevHalt.Theory.Splitter.Core

/-!
# RevHalt.Theory.Splitter.Auxi

**Auxiliary definitions for internal/demo use only.**

This module contains deprecated or non-spec-compliant definitions:
- `SplitterEquiv` (depth-1 equivalence, not ObsEq)
- `isTrivial` (deprecated, use SyntaxTrivial/TrivialObs)
- `Atomic`, `isAtomicRelative`, `Prime_RH_aux` (based on SplitterEquiv)

For spec-compliant code, use the definitions in Core.lean:
- `ObsEq` for equivalence
- `TrivialObs` for triviality
- `AtomicObs` for atomicity

These aux definitions are kept only for compositional proofs and demos.
-/

namespace RevHalt.Splitter.Auxi

open RevHalt.Splitter

variable (Pos : Type)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Shallow Equivalence (Depth 1)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Shallow depth-1 equivalence. NOT the official spec equivalence.
    For spec-compliant code, use `ObsEq` instead. -/
def SplitterEquiv (A B : Splitter Pos) : Prop :=
  ∀ I n m,
    (∃ J ∈ A.split I, Sat Pos J n ∧ Sat Pos J m) ↔
    (∃ K ∈ B.split I, Sat Pos K n ∧ Sat Pos K m)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Deprecated Triviality
-- ═══════════════════════════════════════════════════════════════════════════════

/-- [Deprecated] Use `SyntaxTrivial` or `TrivialObs` instead. -/
def isTrivial (S : Splitter Pos) : Prop :=
  ∀ I, ∀ J ∈ S.split I, (∀ n, Sat Pos I n ↔ Sat Pos J n)

def isNontrivial (S : Splitter Pos) : Prop := ¬ isTrivial Pos S

-- ═══════════════════════════════════════════════════════════════════════════════
-- Aux Atomicity (via SplitterEquiv)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Atomicity via SplitterEquiv. NOT official - use `AtomicObs`. -/
def Atomic (S : Splitter Pos) : Prop :=
  ∀ A B : Splitter Pos, SplitterEquiv Pos S (compose Pos A B) →
    isTrivial Pos A ∨ isTrivial Pos B

/-- Atomicity relative to admissible class. -/
def isAtomicRelative (S : Splitter Pos) (Adm : Splitter Pos → Prop) : Prop :=
  isNontrivial Pos S ∧
  Adm S ∧
  ∀ A B : Splitter Pos, Adm A → Adm B → isNontrivial Pos A → isNontrivial Pos B →
    SplitterEquiv Pos (compose Pos A B) S →
    (SplitterEquiv Pos A S ∨ SplitterEquiv Pos B S)

def isAtomic (S : Splitter Pos) : Prop := isAtomicRelative Pos S (fun _ => True)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Prime_RH (Aux version)
-- ═══════════════════════════════════════════════════════════════════════════════

variable (SplitFamily : ℕ → Splitter ℕ)
variable (Adm : Splitter ℕ → Prop)

/-- [Aux] Prime_RH via aux atomicity. NOT official - use AtomicObs for spec. -/
def Prime_RH_aux (p : ℕ) : Prop := isAtomicRelative ℕ (SplitFamily p) Adm

-- ═══════════════════════════════════════════════════════════════════════════════
-- Composition Theorems (use SplitterEquiv)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: We use simp for flatMap [x] = x directly to avoid duplication with Core.flatMap_singleton

/-- Id ⊗ S ≈ S (left identity). -/
theorem id_compose_left (S : Splitter Pos) :
    SplitterEquiv Pos (compose Pos (IdSplitter Pos) S) S := by
  intro I n m
  have h_eq : (compose Pos (IdSplitter Pos) S).split I = S.split I := by
    simp only [compose, IdSplitter, List.flatMap_singleton]
  simp only [h_eq]

/-- S ⊗ Id ≈ S (right identity). -/
theorem id_compose_right (S : Splitter Pos) :
    SplitterEquiv Pos (compose Pos S (IdSplitter Pos)) S := by
  intro I n m
  have h_eq : (compose Pos S (IdSplitter Pos)).split I = S.split I := by
    simp only [compose, IdSplitter]
    induction S.split I with
    | nil => simp [List.flatMap]
    | cons head tail ih =>
      simp only [List.flatMap_cons, List.singleton_append]
      rw [ih]
  simp only [h_eq]

/-- Composition is associative. -/
theorem compose_assoc (A B C : Splitter Pos) :
    SplitterEquiv Pos (compose Pos (compose Pos A B) C) (compose Pos A (compose Pos B C)) := by
  intro I n m
  have h_eq : (compose Pos (compose Pos A B) C).split I = (compose Pos A (compose Pos B C)).split I := by
    show ((A.split I).flatMap B.split).flatMap C.split = (A.split I).flatMap (fun K => (B.split K).flatMap C.split)
    set l := A.split I with hl
    induction l with
    | nil => simp [List.flatMap]
    | cons head tail ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [ih]
  simp only [h_eq]

end RevHalt.Splitter.Auxi

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Splitter.Auxi.SplitterEquiv
#print axioms RevHalt.Splitter.Auxi.isTrivial
#print axioms RevHalt.Splitter.Auxi.Atomic
#print axioms RevHalt.Splitter.Auxi.Prime_RH_aux
