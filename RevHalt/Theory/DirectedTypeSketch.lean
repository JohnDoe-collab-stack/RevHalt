/-!
# Directed Type Theory: A Sketch

This file outlines a potential refoundation of Type Theory where "direction" is primitive
and "equality" (in the sense of HoTT) is a derived structure requiring specific axioms.

We start not with `x = y` (symmetric), but with `x ~> y` (directed reachability).
-/

universe u v

/--
## 1. The Primitive: Directed Hom Type
Instead of `Eq`, we have `Hom`, representing a directed path or "execution".
-/
class DirectedType (A : Type u) where
  Hom : A → A → Type v
  id (x : A) : Hom x x
  comp {x y z : A} : Hom x y → Hom y z → Hom x z

/--
## 2. The Derived Identity (Isomorphism)
Standard equality requires paths to be invertible.
We define `Iso` as a pair of inverse directed paths.
-/
structure Iso {A : Type u} [DirectedType A] (x y : A) where
  fwd : DirectedType.Hom x y
  bwd : DirectedType.Hom y x
  -- In a full theory, we would need coherence laws here (iso_l, iso_r).
  -- But wait! Coherence requires identifying `comp fwd bwd` with `id`.
  -- This requires a notion of "path equality"... which is what we are defining!

  -- This circle suggests that `Iso` is witnessing "Reversibility".

/--
## 3. The Computation/Homotopy Layer
To talk about "laws" (like associativity or invertibility), we need
a 2-dimensional structure: deformations between paths.
-/
class DirectedHomotopyType (A : Type u) extends DirectedType A where
  -- 2-morphisms: deformations between parallel paths
  Def {x y : A} (f g : Hom x y) : Type v
  idDef {x y : A} (f : Hom x y) : Def f f
  compDef {x y : A} {f g h : Hom x y} : Def f g → Def g h → Def f h
  -- Vertical and horizontal composition would be added here...

/--
## 4. The "Flatness" Condition (C2)
HoTT assumes that any "loop of deformations" (e.g. going around an identity) implies
that the transport is trivial. In our Directed Theory, this must be explicit.
-/
def IsFlat {A : Type u} [DirectedHomotopyType A] : Prop :=
  ∀ {x : A} (p : DirectedType.Hom x x), DirectedHomotopyType.Def p (DirectedType.id x) →
  -- "The transport/holonomy along p is the identity relation"
  -- This requires the semantic layer (Prop-valued relations) to state operational flatness.
  True -- Placeholder

/--
## 5. Recovering HoTT
A type `A` is a "HoTT Type" (Groupoid) if:
1. It is `Reversible`: Every `Hom x y` has a constructible inverse.
2. It is `Flat`: The holonomy of contractible loops is trivial.
-/
class HoTT_Type (A : Type u) extends DirectedHomotopyType A where
  reversible : ∀ {x y : A} (f : Hom x y), ∃ g : Hom y x, Nonempty (Def (DirectedType.comp f g) (DirectedType.id x))
  flat : IsFlat -- (Formalized properly)

/-!
## Conclusion of the Sketch
In this system:
- `DirectedType` is the general case (includes irreversible computations).
- `HoTT_Type` is the special "well-behaved" sub-universe where equality behaves like geometry.
- The "Obstruction" to becoming a HoTT type is precisely what `PrimitiveHolonomy` measures.
-/
