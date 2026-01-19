import RevHalt.Theory.TheoryDynamics
import RevHalt.Theory.TheoryDynamics_ProofCarrying
import RevHalt.Theory.TheoryDynamics_ComplexityBounds
import Mathlib.Data.List.Basic

namespace RevHalt.CanonizationWC

open RevHalt
open RevHalt.ProofCarrying.Witness

section Variables

/-
  We fix the proposition type `PropT` to be generic, but it will be `ℕ` for TSP.
-/
variable {PropT : Type}

-- A generic notion of "ground truth" for valid instances/propositions.
variable (IsTrue : PropT → Prop)

-- Abstract Checkers.
variable (ChecksDerivation : Set PropT → PropT → DerivationCode → Bool)
variable (ChecksWitness    : PropT → List ℕ → Bool)
variable (decodeList       : ℕ → List ℕ)




/--
  **PosCompleteWC**: Positive Completeness in WC terms.
  If `p` is true, then it is WC-provable in `Γ`.
  This is the bridge between "Model Truth" and "Derivability".
-/
structure PosCompleteWC (Γ : Set PropT) : Prop where
  pos : ∀ p, IsTrue p → ProvableWC (ChecksDerivation:=ChecksDerivation)
                         (ChecksWitness:=ChecksWitness)
                         (decodeList:=decodeList) Γ p

/--
  **BoundPosWC**: Constructive Bound on WC Derivations.
  This is the **Layer 2 Data Object** (precursor to PolyPosWC).
  It asserts that if `p` is true, a "short" derivation exists (code < B(size p)).
-/
structure BoundPosWC (Γ : Set PropT) (size : PropT → ℕ) : Type where
  B : ℕ → ℕ
  pos_short :
    ∀ p, IsTrue p →
      ∃ d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p,
        d.code < B (size p)

/--
  A local completeness lemma for `findBounded`.
  If a derivation exists with code < bound, `findBounded` will find *some* derivation.
-/
theorem findBounded_complete_local
    {Γ : Set PropT}
    {ChecksDerivation : Set PropT → PropT → DerivationCode → Bool}
    {ChecksWitness : PropT → List ℕ → Bool}
    {decodeList : ℕ → List ℕ}
    (p : PropT) (bound : ℕ)
    (d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p)
    (hd : d.code < bound) :
    (WCDerivation.findBounded ChecksDerivation ChecksWitness decodeList Γ p bound).isSome := by
  exact WCDerivation.findBounded_complete ChecksDerivation ChecksWitness decodeList Γ p bound d hd

/--
  **Find_of_Bound**: Constructive Search from Bound.
  Given a `BoundPosWC` object, we can construct a computable search procedure.
  This is the Layer 2 -> Layer 1 bridge.
-/
def Find_of_Bound
    {Γ : Set PropT} {size : PropT → ℕ}
    (bd : BoundPosWC (IsTrue:=IsTrue)
                     (ChecksDerivation:=ChecksDerivation)
                     (ChecksWitness:=ChecksWitness)
                     (decodeList:=decodeList)
                     Γ size)
    (p : PropT) : Option (List ℕ) :=
  (WCDerivation.findBounded ChecksDerivation ChecksWitness decodeList Γ p (bd.B (size p))).map
    (WCDerivation.witness ChecksDerivation ChecksWitness decodeList)

/--
  **Correctness**: If Find returns a witness, it satisfies ChecksWitness.
-/
theorem Find_of_Bound_correct
    {Γ : Set PropT} {size : PropT → ℕ}
    (bd : BoundPosWC (IsTrue:=IsTrue)
                     (ChecksDerivation:=ChecksDerivation)
                     (ChecksWitness:=ChecksWitness)
                     (decodeList:=decodeList)
                     Γ size)
    (p : PropT) :
    ∀ w, Find_of_Bound (IsTrue:=IsTrue)
                       (ChecksDerivation:=ChecksDerivation)
                       (ChecksWitness:=ChecksWitness)
                       (decodeList:=decodeList)
                       bd p = some w →
         ChecksWitness p w = true := by
  intro w h
  unfold Find_of_Bound at h
  cases hD : WCDerivation.findBounded ChecksDerivation ChecksWitness decodeList Γ p (bd.B (size p))
  · simp [hD] at h -- contradiction
  · rename_i d
    simp [hD] at h
    -- Option.map ... = some w  implies  witness ... d = w
    have hw : WCDerivation.witness ChecksDerivation ChecksWitness decodeList d = w := by
      simpa using h
    -- d is valid
    have hv := d.valid
    simp [ChecksWC, Bool.and_eq_true] at hv
    -- substitute
    rw [←hw]
    exact hv.2

/--
  **Completeness**: If `p` is true, Find returns `some witness`.
  Guaranteed by `BoundPosWC` providing a short derivation.
-/
theorem Find_of_Bound_complete
    {Γ : Set PropT} {size : PropT → ℕ}
    (bd : BoundPosWC (IsTrue:=IsTrue)
                     (ChecksDerivation:=ChecksDerivation)
                     (ChecksWitness:=ChecksWitness)
                     (decodeList:=decodeList)
                     Γ size)
    (p : PropT) :
    IsTrue p → (Find_of_Bound (IsTrue:=IsTrue)
                              (ChecksDerivation:=ChecksDerivation)
                              (ChecksWitness:=ChecksWitness)
                              (decodeList:=decodeList)
                              bd p).isSome := by
  intro hTrue
  -- 1. BoundPosWC guarantees a short derivation exists
  obtain ⟨d, hdlt⟩ := bd.pos_short p hTrue
  -- 2. Local completeness guarantees findBounded finds it (or another)
  have hFound := findBounded_complete_local p (bd.B (size p)) d hdlt
  -- 3. Conclusion
  unfold Find_of_Bound
  simpa using hFound


/-!
  ## 3) Compression and Closure (Option C)

  We separate "Completeness" (Layer 2) from "Compression/Complexity" (Price of P).

  * `PosCompleteWC` : If true, then provable.
  * `PolyCompressionWC` : If provable, then short (polynomial) derivation exists.
  * `PolyPosWC` : If true, then short derivation exists (The combination).
-/

/--
  **CompressionWC**: "If p is WC-provable, there exists a derivation bounded by B(size p)."
  This represents the "Price of P" as a conditional property of the proof system.
-/
structure CompressionWC (Γ : Set PropT) (size : PropT → ℕ) : Type where
  B : ℕ → ℕ
  compress :
    ∀ p : PropT,
      ProvableWC (PropT:=PropT)
        (ChecksDerivation:=ChecksDerivation)
        (ChecksWitness:=ChecksWitness)
        (decodeList:=decodeList)
        Γ p →
      ∃ d : WCDerivation ChecksDerivation ChecksWitness decodeList Γ p,
        d.code < B (size p)

/--
  **PolyCompressionWC**: The compression function B is polynomial.
  This is the precise statement of "Price of P" as a complexity hypothesis.
-/
structure PolyCompressionWC (Γ : Set PropT) (size : PropT → ℕ)
    : Type extends CompressionWC (PropT:=PropT) (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness) (decodeList:=decodeList) Γ size where
  B_poly : RevHalt.Complexity.IsPoly B

/--
  **Closure Lemma**: PosComplete + PolyCompression => PolyPosWC.
  This closes the loop: Logical Completeness (from Dynamics) + Complexity Hypothesis => Constructive Bounds.
-/
def PolyPosWC_of_PosComplete_and_PolyCompression
    {Γ : Set PropT} {size : PropT → ℕ}
    (pos : PosCompleteWC
      (PropT:=PropT) (IsTrue:=IsTrue)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness)
      (decodeList:=decodeList)
      Γ)
    (pc : PolyCompressionWC
      (PropT:=PropT)
      (ChecksDerivation:=ChecksDerivation)
      (ChecksWitness:=ChecksWitness)
      (decodeList:=decodeList)
      Γ size) :
    @RevHalt.Complexity.PolyPosWC PropT Γ ChecksDerivation ChecksWitness decodeList size IsTrue := {
  B := pc.B
  B_poly := pc.B_poly
  pos_short := by
    intro p hTrue
    -- 1. PosCompleteWC gives ProvableWC
    have hp : ProvableWC (PropT:=PropT)
        (ChecksDerivation:=ChecksDerivation)
        (ChecksWitness:=ChecksWitness)
        (decodeList:=decodeList)
        Γ p :=
      pos.pos p hTrue
    -- 2. PolyCompressionWC "compresses" it into a bounded derivation
    exact pc.compress p hp
}

end Variables

end RevHalt.CanonizationWC
