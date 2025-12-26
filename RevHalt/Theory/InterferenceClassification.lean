/-
  RevHalt/Theory/InterferenceClassification.lean

  Classification + unification “shell” (axiom-free, constructive):

  * No `Prop ∨ Prop` stored as “dichotomy”.
  * Classification is by *computed tags* (ParKind / Polarity / SeqKind).
  * The only thing you must provide from your RevHalt Compatibility layer
    is an `InterferenceAlgebra` instance (i.e. operations + laws + tags).
-/

import RevHalt.Base

namespace RevHalt

/-- Parallel tag: idempotent (“sup-like”) vs cancellative (“+”-like). -/
inductive ParKind | idem | cancel
deriving DecidableEq, Repr

/-- Polarity tag: max-oriented vs min-oriented. -/
inductive Polarity | max | min
deriving DecidableEq, Repr

/-- Constructive witness that `op` is not idempotent. -/
structure NonIdemWitness (S : Type) (op : S → S → S) : Type where
  x : S
  hx : op x x ≠ x

/-- Sequential tag: idempotent vs non-idempotent (with witness). -/
inductive SeqKind (S : Type) (op : S → S → S)
  | idem
  | nonidem (w : NonIdemWitness S op)
deriving Repr

/-- The 4 canonical arithmetic shapes. -/
inductive CanonicalPair
  | maxPlus   -- (max, +)
  | minPlus   -- (min, +)
  | plusPlus  -- (+, +)
  | plusMax   -- (+, max)
deriving DecidableEq, Repr

/-- Core “interference algebra” laws (what you derive from Compatibility). -/
structure InterferenceCore where
  S     : Type
  le    : S → S → Prop
  opPar : S → S → S   -- ⊕
  opSeq : S → S → S   -- ⊙
  zero  : S
  one   : S

  -- preorder
  le_refl  : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z

  -- monotone
  mono_par : ∀ a b a' b', le a a' → le b b' → le (opPar a b) (opPar a' b')
  mono_seq : ∀ a b a' b', le a a' → le b b' → le (opSeq a b) (opSeq a' b')

  -- ⊕ commutative monoid
  par_assoc : ∀ a b c, opPar (opPar a b) c = opPar a (opPar b c)
  par_comm  : ∀ a b, opPar a b = opPar b a
  par_zero  : ∀ a, opPar a zero = a

  -- ⊙ commutative monoid
  seq_assoc : ∀ a b c, opSeq (opSeq a b) c = opSeq a (opSeq b c)
  seq_one_l : ∀ a, opSeq one a = a
  seq_one_r : ∀ a, opSeq a one = a
  seq_comm  : ∀ a b, opSeq a b = opSeq b a

  -- lax interchange (from Compatibility)
  interchange_lax :
    ∀ a b c d,
      le (opSeq (opPar a b) (opPar c d))
         (opPar (opPar (opSeq a c) (opSeq a d))
                (opPar (opSeq b c) (opSeq b d)))

/--
InterferenceAlgebra = Core + computed tags + “bridge lemmas” (no axioms).

You derive:
* tags (parKind/pol/seqKind) from your RevHalt dynamics/compatibility invariants,
* plus the corresponding proofs triggered by each tag.
-/
structure InterferenceAlgebra extends InterferenceCore where
  parKind : ParKind
  pol     : Polarity
  seqKind : SeqKind S opSeq

  par_idem_of_kind :
    parKind = ParKind.idem → (∀ x, opPar x x = x)

  par_cancel_of_kind :
    parKind = ParKind.cancel → (∀ x y z, opPar x y = opPar x z → y = z)

  seq_idem_of_kind :
    seqKind = SeqKind.idem → (∀ x, opSeq x x = x)

/-- Canonical pair chosen *constructively* from tags. -/
def choosePair (A : InterferenceAlgebra) : CanonicalPair :=
  match A.parKind, A.pol, A.seqKind with
  | ParKind.idem, Polarity.max, _ => CanonicalPair.maxPlus
  | ParKind.idem, Polarity.min, _ => CanonicalPair.minPlus
  | ParKind.cancel, _, SeqKind.idem => CanonicalPair.plusMax
  | ParKind.cancel, _, SeqKind.nonidem _ => CanonicalPair.plusPlus

/-- What it means for the algebra to satisfy a given canonical shape. -/
def satisfies (A : InterferenceAlgebra) : CanonicalPair → Prop
  | CanonicalPair.maxPlus =>
      (∀ x, A.opPar x x = x) ∧ (∀ x y, A.opSeq x y = A.opSeq y x)
  | CanonicalPair.minPlus =>
      (∀ x, A.opPar x x = x) ∧ (∀ x y, A.opSeq x y = A.opSeq y x)
  | CanonicalPair.plusMax =>
      (∀ x y z, A.opPar x y = A.opPar x z → y = z) ∧ (∀ x, A.opSeq x x = x)
  | CanonicalPair.plusPlus =>
      (∀ x y z, A.opPar x y = A.opPar x z → y = z) ∧ (∃ x, A.opSeq x x ≠ x)

/--
Classification theorem (constructive, no classical split on Props):

Once you provide `A : InterferenceAlgebra` from your RevHalt Compatibility layer,
classification is automatic.
-/
theorem classification (A : InterferenceAlgebra) :
    satisfies A (choosePair A) := by
  cases hpar : A.parKind <;> cases hpol : A.pol <;> cases hseq : A.seqKind
  · -- idem/max/idem
    dsimp [choosePair, satisfies]
    refine ⟨A.par_idem_of_kind rfl, ?_⟩
    intro x y; exact A.seq_comm x y
  · -- idem/max/nonidem
    dsimp [choosePair, satisfies]
    refine ⟨A.par_idem_of_kind rfl, ?_⟩
    intro x y; exact A.seq_comm x y
  · -- idem/min/idem
    dsimp [choosePair, satisfies]
    refine ⟨A.par_idem_of_kind rfl, ?_⟩
    intro x y; exact A.seq_comm x y
  · -- idem/min/nonidem
    dsimp [choosePair, satisfies]
    refine ⟨A.par_idem_of_kind rfl, ?_⟩
    intro x y; exact A.seq_comm x y
  · -- cancel/max/idem -> plusMax
    dsimp [choosePair, satisfies]
    refine ⟨A.par_cancel_of_kind rfl, A.seq_idem_of_kind rfl⟩
  · -- cancel/max/nonidem -> plusPlus
    dsimp [choosePair, satisfies]
    refine ⟨A.par_cancel_of_kind rfl, ?_⟩
    refine ⟨hseq.w.x, hseq.w.hx⟩
  · -- cancel/min/idem -> plusMax
    dsimp [choosePair, satisfies]
    refine ⟨A.par_cancel_of_kind rfl, A.seq_idem_of_kind rfl⟩
  · -- cancel/min/nonidem -> plusPlus
    dsimp [choosePair, satisfies]
    refine ⟨A.par_cancel_of_kind rfl, ?_⟩
    refine ⟨hseq.w.x, hseq.w.hx⟩

/-- Existence form (sometimes what you want downstream). -/
theorem classification_exists (A : InterferenceAlgebra) :
    ∃ cp : CanonicalPair, satisfies A cp :=
  ⟨choosePair A, classification A⟩

end RevHalt
