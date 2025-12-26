import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.SetTheory.Formula

First-Order Logic (FOL) syntax for Set Theory with De Bruijn indices.
Includes:
- `Term` (variables `#k`)
- `Formula` (membership, equality, quantifiers, connectives)
- `lift` (shifting indices for safe scope traversal)
- `subst` (parallel substitution)
- `subst0` (single variable substitution / beta-reduction)

This infrastructure enables rigorous handling of bound variables and axiom schemas.
-/

namespace RevHalt.SetTheory

/-- Terms: only variables (De Bruijn indices). -/
inductive Term where
  | var : Nat → Term
  deriving Repr, DecidableEq, Inhabited

/--
  Formulas in the language `∈`, `=`.
  De Bruijn indices: `var 0` is the innermost bound variable.
-/
inductive Formula where
  | mem : Term → Term → Formula
  | eq  : Term → Term → Formula
  | fal : Formula
  | imp : Formula → Formula → Formula
  | all : Formula → Formula
  deriving Repr, DecidableEq, Inhabited

open Term Formula

-- =====================================================================================
-- 1. Lifting (Shifting Indices)
-- =====================================================================================

/--
  `lift_term n k t`: shift free variables ≥ k by n.
  Used when a term moves under n new binders.
-/
def lift_term (n k : Nat) (t : Term) : Term :=
  match t with
  | var i => if i < k then var i else var (i + n)

/--
  `lift n k φ`: shift free variables ≥ k by n in formula φ.
  When going under `all`, k increases by 1 (binding depth).
-/
def lift (n k : Nat) (φ : Formula) : Formula :=
  match φ with
  | mem t1 t2 => mem (lift_term n k t1) (lift_term n k t2)
  | eq t1 t2  => eq (lift_term n k t1) (lift_term n k t2)
  | fal       => fal
  | imp p q   => imp (lift n k p) (lift n k q)
  | all p     => all (lift n (k + 1) p)

/-- `lift0 n φ`: standard lift of n levels at depth 0. -/
def lift0 (n : Nat) (φ : Formula) : Formula := lift n 0 φ

-- =====================================================================================
-- 2. Substitution
-- =====================================================================================

/--
  `subst_term s t`: apply substitution `s : Nat → Term` to term `t`.
-/
def subst_term (s : Nat → Term) (t : Term) : Term :=
  match t with
  | var i => s i

/--
  `shift_subst s`: lift the codomain of substitution `s` by 1.
  Used when moving substitution under a binder.
  Map index 0 to 0 (the new bound var), and map i+1 to s(i) lifted by 1.
-/
def shift_subst (s : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => lift_term 1 0 (s n)

/--
  `subst s φ`: parallel substitution in formula.
-/
def subst (s : Nat → Term) (φ : Formula) : Formula :=
  match φ with
  | mem t1 t2 => mem (subst_term s t1) (subst_term s t2)
  | eq t1 t2  => eq (subst_term s t1) (subst_term s t2)
  | fal       => fal
  | imp p q   => imp (subst s p) (subst s q)
  | all p     => all (subst (shift_subst s) p)

/--
  `subst0 t φ`: Substitute `t` for bound variable 0 in `φ`.
  Corresponds to `φ[t/x]` where x is the outermost binder.
  The substitution maps:
    0 -> t
    i+1 -> i  (decrement others as one binder is removed)
-/
def cons_subst (t : Term) : Nat → Term
  | 0 => t
  | n + 1 => var n

def subst0 (t : Term) (φ : Formula) : Formula :=
  subst (cons_subst t) φ

-- =====================================================================================
-- 3. Derived Connectives & Notations
-- =====================================================================================

def not (p : Formula) : Formula := imp p fal
def and (p q : Formula) : Formula := not (imp p (not q))
def or  (p q : Formula) : Formula := imp (not p) q
def iff (p q : Formula) : Formula := and (imp p q) (imp q p)
def ex  (p : Formula) : Formula := not (all (not p))

-- String representation (variables as #k)
def Term.toString : Term → String
  | var k => s!"#{k}"

partial def Formula.toString : Formula → String
  | mem t1 t2 => s!"({t1.toString} ∈ {t2.toString})"
  | eq t1 t2  => s!"({t1.toString} = {t2.toString})"
  | fal       => "⊥"
  | imp p q   => s!"({p.toString} → {q.toString})"
  | all p     => s!"(∀ {p.toString})"

instance : ToString Term := ⟨Term.toString⟩
instance : ToString Formula := ⟨Formula.toString⟩

end RevHalt.SetTheory
