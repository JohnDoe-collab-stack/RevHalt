import RevHalt.Theory.SetTheory.Axioms

/-!
# RevHalt.Theory.SetTheory.Deduction

Standard Hilbert-style Deduction System for FOL.
Defines `Derives Γ φ` (written Γ ⊢ φ).

Includes:
- Logical Axioms (K, S, Contraposition, Quantifier axioms)
- Inference Rules (MP, Gen)
- ZFC Provability: `ZFC_Provable φ := Derives {φ | IsZFC_Axiom φ} φ`
-/

namespace RevHalt.SetTheory

open Formula Term

-- =====================================================================================
-- 1. Logical Axioms
-- =====================================================================================

/--
  Minimal Logic Axioms (K, S).
-/
def AxK (p q : Formula) : Formula :=
  imp p (imp q p)

def AxS (p q r : Formula) : Formula :=
  imp (imp p (imp q r)) (imp (imp p q) (imp p r))

/--
  Contraposition / Falsehood (sufficient for CPL with bot).
  (¬p → ¬q) → (q → p)
  Note: ¬p is p → ⊥.
-/
def AxContra (p q : Formula) : Formula :=
  imp (imp (not p) (not q)) (imp q p)

/--
  Quantifier Axiom: ∀x φ → φ[t/x]
  Specific instance: ∀x φ → φ[y/x] (instantiation with a variable).
  More generally with terms.
  We implement: `(∀ φ) → subst0 t φ`
-/
def AxInst (t : Term) (φ : Formula) : Formula :=
  imp (all φ) (subst0 t φ)

/--
  Quantifier Distribution (K for ∀):
  ∀(p → q) → (∀p → ∀q)
-/
def AxDist (p q : Formula) : Formula :=
  imp (all (imp p q)) (imp (all p) (all q))

/--
  Vacuous Quantification:
  p → ∀p   (if variable 0 is not free in p)
  This requires a `IsFree` predicate or careful handling.
  Standard system: `p → ∀ (lift0 1 p)`
-/
def AxVacuous (p : Formula) : Formula :=
  imp p (all (lift0 1 p))

/--
  Equality Axioms:
  1. Reflexivity: x = x
  2. Substitutivity: x = y → (φ(x) → φ(y))
-/
def AxRefl : Formula :=
  eq (var 0) (var 0)

def AxEqSubst (t1 t2 : Term) (_ : Formula) : Formula :=
  -- This formulation is tricky without context.
  -- Simplified: x=y → (x∈z → y∈z) ∧ (z∈x → z∈y) is enough with extensionality.
  imp (eq t1 t2)
    (and
      (all (iff (mem (var 0) (lift_term 1 0 t1)) (mem (var 0) (lift_term 1 0 t2))))
      (all (iff (mem (lift_term 1 0 t1) (var 0)) (mem (lift_term 1 0 t2) (var 0))))
    )

inductive IsLogicalAxiom : Formula → Prop where
  | K   : ∀ p q, IsLogicalAxiom (AxK p q)
  | S   : ∀ p q r, IsLogicalAxiom (AxS p q r)
  | C   : ∀ p q, IsLogicalAxiom (AxContra p q)
  | I   : ∀ t φ, IsLogicalAxiom (AxInst t φ)
  | D   : ∀ p q, IsLogicalAxiom (AxDist p q)
  | V   : ∀ p, IsLogicalAxiom (AxVacuous p)
  | Ref : IsLogicalAxiom AxRefl
  | Eq  : ∀ t1 t2, IsLogicalAxiom (AxEqSubst t1 t2 Formula.fal) -- Simplified Eq Subst

-- =====================================================================================
-- 2. Derivation System
-- =====================================================================================

/--
  `Derives Γ φ`: φ is provable from assumptions Γ.
-/
inductive Derives (Γ : Set Formula) : Formula → Prop where
  /-- Assumption: φ ∈ Γ implies Γ ⊢ φ -/
  | hyp : ∀ {φ}, φ ∈ Γ → Derives Γ φ
  /-- Logical Axiom: Λ implies Γ ⊢ Λ -/
  | log : ∀ {φ}, IsLogicalAxiom φ → Derives Γ φ
  /-- Modus Ponens: Γ ⊢ p → q, Γ ⊢ p implies Γ ⊢ q -/
  | mp  : ∀ {p q}, Derives Γ (imp p q) → Derives Γ p → Derives Γ q
  /-- Generalization: Γ ⊢ φ implies Γ ⊢ ∀φ
      Restriction: Only valid if variable 0 is not free in Γ.
      For simplicity in this ZFC formalization (where Γ is closed axioms),
      unconditional Gen is acceptable or we assume Γ is a set of sentences.
  -/
  | gen : ∀ {p}, Derives Γ p → Derives Γ (all p)

-- =====================================================================================
-- 3. ZFC Provability
-- =====================================================================================

def ZFC_Set : Set Formula := { φ | IsZFC_Axiom φ }

/--
  **ZFC Provability**:
  The formal proof relation for the system.
-/
def ZFC_Provable (φ : Formula) : Prop :=
  Derives ZFC_Set φ

/--
  Consistency check (statement).
  ZFC ⊬ ⊥
-/
def ZFC_Consistent : Prop :=
  ¬ ZFC_Provable Formula.fal

end RevHalt.SetTheory
