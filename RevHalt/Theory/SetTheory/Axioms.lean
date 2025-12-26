import RevHalt.Theory.SetTheory.Formula

/-!
# RevHalt.Theory.SetTheory.Axioms

Authentic ZFC Axioms defined using the De Bruijn FOL engine.
We define `IsZFC_Axiom : Formula → Prop` as the set of all ZFC axioms.
This includes:
- Finite Axioms (Extensionality, Pairing, Union, etc.)
- Axiom Schemas (Separation, Replacement) instantiated via `subst`.

De Bruijn Convention:
- `var 0`, `var 1`, ... are bound variables relative to the enclosing `all`.
-/

namespace RevHalt.SetTheory

open Term Formula

-- =====================================================================================
-- 1. Finite Axioms
-- =====================================================================================

/--
  Extensionality: ∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y)
  - x is bound at depth 1 (var 1)
  - y is bound at depth 0 (var 0)
  - z is bound at depth 0 inside the inner ∀ (var 0), lifting others
-/
def AxExtensionality : Formula :=
  all (all (imp
    (all (iff (mem (var 0) (var 2)) (mem (var 0) (var 1))))
    (eq (var 1) (var 0))
  ))

/-- Empty Set: ∃x ∀y (y ∉ x) -/
def AxEmptySet : Formula :=
  ex (all (not (mem (var 0) (var 1))))

/-- Pairing: ∀x ∀y ∃z (x ∈ z ∧ y ∈ z) -/
def AxPairing : Formula :=
  all (all (ex (and (mem (var 2) (var 0)) (mem (var 1) (var 0)))))

/-- Union: ∀x ∃y ∀z (z ∈ y ↔ ∃w (w ∈ x ∧ z ∈ w)) -/
def AxUnion : Formula :=
  all (ex (all (iff
    (mem (var 0) (var 1))
    (ex (and (mem (var 0) (var 3)) (mem (var 1) (var 0))))
  )))

/-- Power Set: ∀x ∃y ∀z (z ∈ y ↔ z ⊆ x) where z ⊆ x is ∀w (w ∈ z → w ∈ x) -/
def subset (t1 t2 : Term) : Formula :=
  all (imp (mem (var 0) (lift_term 1 0 t1)) (mem (var 0) (lift_term 1 0 t2)))

def AxPowerSet : Formula :=
  all (ex (all (iff
    (mem (var 0) (var 1))
    (subset (var 0) (var 2))
  )))

/-- Infinity: ∃x (∅ ∈ x ∧ ∀y (y ∈ x → y ∪ {y} ∈ x)) -/
-- Note: This is complex to write fully without "sugar", so we state existence of inductive set.
-- ∃x ( (∃e e∈x ∧ ∀z z∉e) ∧ ∀y∈x ∃s∈x ∀z (z∈s ↔ z∈y ∨ z=y) )
def AxInfinity : Formula :=
  ex (and
    -- ∅ ∈ x
    (ex (and (mem (var 0) (var 1)) (all (not (mem (var 0) (var 1))))))
    -- ∀y ∈ x, successor ∈ x
    (all (imp (mem (var 0) (var 1))
      (ex (and (mem (var 0) (var 2))
        (all (iff (mem (var 0) (var 1)) (or (mem (var 0) (var 2)) (eq (var 0) (var 2)))))
      ))
    ))
  )

/-- Foundation (Regularity): ∀x (x ≠ ∅ → ∃y ∈ x (x ∩ y = ∅)) -/
def AxFoundation : Formula :=
  all (imp
    (ex (mem (var 0) (var 1))) -- x ≠ ∅
    (ex (and (mem (var 0) (var 1)) -- y ∈ x
      (all (not (and (mem (var 0) (var 1)) (mem (var 0) (var 2))))) -- x ∩ y = ∅
    ))
  )

-- =====================================================================================
-- 2. Axiom Schemas
-- =====================================================================================

/--
  Separation Schema: ∀w₁...wₖ ∀x ∃y ∀z (z ∈ y ↔ z ∈ x ∧ φ(z, w₁...wₖ))
  Defined for any formula φ.
  We handle the closure over parameters w₁...wₖ implicitly by allowing φ to have free vars > 0.
  Then the schema is: ∀x ∃y ∀z (z ∈ y ↔ z ∈ x ∧ φ[z/var 0, w/lift])
-/
def AxSeparationSchema (φ : Formula) : Formula :=
  -- We assume φ has free variables.
  -- The schema statement is: ∀x ∃y ∀z (z ∈ y ↔ z ∈ x ∧ φ(z))
  -- Inside the inner ∀z (depth 2):
  -- x is var 2. y is var 1. z is var 0.
  -- φ expects z at index 0 and parameters at higher indices.
  -- We must lift φ by 3 (for x, y, z binders) to keep parameters safe,
  -- but we want z to be bound by the inner quantifier.
  -- Actually, standard practice: φ(z) has z free (var 0).
  -- When we embed it in `... ∧ φ`, we are at logic depth 3 (x,y,z bound).
  -- So we lift parameters by 3, but z should refer to `var 0`.
  let phi_lifted := lift 3 1 φ -- lift vars >= 1 by 3. Var 0 remains 0 (z).
  all (ex (all (iff
    (mem (var 0) (var 1))
    (and (mem (var 0) (var 2)) phi_lifted)
  )))

/--
  Replacement Schema: ∀x (∀u∈x ∃!v φ(u,v) → ∃y ∀v (v∈y ↔ ∃u∈x φ(u,v)))
  This matches the "Functional Image" version.
  φ has free variables.
-/
def AxReplacementSchema (φ : Formula) : Formula :=
  all (imp
    -- Functional(φ) on domain x (var 0)
    (all (imp (mem (var 0) (var 1)) (ex (and (lift 2 2 φ)  -- φ(u,v) where u=var 1, v=var 0.
      (all (imp (lift 1 1 (lift 2 2 φ)) (eq (var 0) (var 1))))) -- Uniqueness
    )))
    -- Then Image Exists
    (ex (all (iff
      (mem (var 0) (var 1))
      (ex (and (mem (var 0) (var 3)) (lift 2 2 φ))) -- ∃u∈x φ(u,v)
    )))
  )

/--
  Axiom of Choice: ∀x (∅ ∉ x ∧ PairwiseDisjoint(x) → ∃c ∀u∈x ∃!w (w ∈ u ∩ c))
  This is compact enough for our purpose.
  Logic:
  PairwiseDisjoint(x): ∀y,z ∈ x (y ≠ z → y ∩ z = ∅)
-/
def AxChoice : Formula :=
  all (imp
    (and
      -- ∅ ∉ x
      (all (imp (mem (var 0) (var 1)) (ex (mem (var 0) (var 1)))))
      -- Pairwise Disjoint: ∀y∈x ∀z∈x (y≠z → y∩z=∅)
      (all (all (imp
        (and (mem (var 1) (var 2)) (mem (var 0) (var 2)))
        (imp (not (eq (var 1) (var 0)))
             (all (not (and (mem (var 0) (var 2)) (mem (var 0) (var 1))))))
      )))
    )
    -- Then Selector Exists: ∃c ∀u∈x ∃!w (w ∈ u ∧ w ∈ c)
    (ex (all (imp (mem (var 0) (var 1))
      (ex (and
        (and (mem (var 0) (var 1)) (mem (var 0) (var 2))) -- w ∈ u ∩ c
        -- Unique
        (all (imp (and (mem (var 0) (var 2)) (mem (var 0) (var 3))) (eq (var 0) (var 1))))
      ))
    )))
  )

inductive IsZFC_Axiom : Formula → Prop where
  | Ext   : IsZFC_Axiom AxExtensionality
  | Empty : IsZFC_Axiom AxEmptySet
  | Pair  : IsZFC_Axiom AxPairing
  | Union : IsZFC_Axiom AxUnion
  | Power : IsZFC_Axiom AxPowerSet
  | Inf   : IsZFC_Axiom AxInfinity
  | Found : IsZFC_Axiom AxFoundation
  -- Schema Instances
  | Sep   : ∀ φ, IsZFC_Axiom (AxSeparationSchema φ)
  | Repl  : ∀ φ, IsZFC_Axiom (AxReplacementSchema φ)
  | Choice : IsZFC_Axiom AxChoice

end RevHalt.SetTheory
