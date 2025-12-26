import Mathlib.Data.Set.Basic

/-!
# RevHalt.Theory.SetTheory.Language

Formal definition of the Language of Set Theory ($\mathcal{L}_{\in}$) in First-Order Logic.
We use a De Bruijn index approach for bound variables for computability and canonical representation.
-/

namespace RevHalt.SetTheory

/--
  The symbols of First-Order Logic with Equality + Membership (∈).
  We use `var k` for free variables (k) and De Bruijn indices for bound ones implicitly in `all`/`ex`.
-/
inductive Term where
  | var : Nat → Term
  deriving Repr, DecidableEq, Inhabited

/--
  Formulas in the language.
  - `mem t1 t2`: t1 ∈ t2
  - `eq t1 t2`: t1 = t2
  - `fal`: False (⊥)
  - `imp p q`: p → q
  - `all p`: ∀ x. p (where x is bound by depth)

  Other connectives (not, and, or, exists) are derived.
-/
inductive Formula where
  | mem : Term → Term → Formula
  | eq  : Term → Term → Formula
  | fal : Formula
  | imp : Formula → Formula → Formula
  | all : Formula → Formula
  deriving Repr, DecidableEq, Inhabited

-- Derived Connectives
def not (p : Formula) : Formula := Formula.imp p Formula.fal
def and (p q : Formula) : Formula := not (Formula.imp p (not q))
def or  (p q : Formula) : Formula := Formula.imp (not p) q
def iff (p q : Formula) : Formula := and (Formula.imp p q) (Formula.imp q p)
def ex  (p : Formula) : Formula := not (Formula.all (not p))

-- String representation for debugging
def Term.toString : Term → String
  | var k => s!"x_{k}"

partial def Formula.toString : Formula → String
  | mem t1 t2 => s!"({t1.toString} ∈ {t2.toString})"
  | eq t1 t2  => s!"({t1.toString} = {t2.toString})"
  | fal       => "⊥"
  | imp p q   => s!"({p.toString} → {q.toString})"
  | all p     => s!"(∀ {p.toString})"

instance : ToString Term := ⟨Term.toString⟩
instance : ToString Formula := ⟨Formula.toString⟩

end RevHalt.SetTheory
