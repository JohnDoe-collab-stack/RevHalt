/-
  RevHalt.Dynamics.Operative.ReductionLibrary

  Generic lemmas + interfaces around the operative many-one reduction `≤ₚ`
  defined in PNP.lean.

  What is fully provable "structurally" (no encoding assumptions):
  - unpacking `correct`
  - uniqueness of the reduction output (from `total` + `functional`)
  - size bounds consequences

  What cannot be proved without extra domain machinery (encodings, closure of LR, etc.)
  is provided as an *interface* (typeclass) so you can plug in concrete instances later:
  - composition of reductions
  - transport of NP across reductions
-/

import RevHalt.Dynamics.Operative.P_NP.PNP

namespace RevHalt.Dynamics.Operative.P_NP.ReductionLibrary

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.PNP

/-! ### §1. NP-hard / NP-complete (internal) -/

/-- Internal NP-hardness (many-one reductions) for RH problems. -/
def NPHard_RH {κ : Type} (Q : RHProblem κ) : Prop :=
  ∀ {ι : Type} (P : RHProblem ι), NP_RH P → (P ≤ₚ Q)

/-- Internal NP-completeness: NP membership + NP-hardness (many-one). -/
def NPComplete_RH {κ : Type} (Q : RHProblem κ) : Prop :=
  NP_RH Q ∧ NPHard_RH Q

theorem NPComplete_of_NP_and_NPHard {κ : Type} (Q : RHProblem κ) :
    NP_RH Q → NPHard_RH Q → NPComplete_RH Q := by
  intro hNP hHard
  exact ⟨hNP, hHard⟩

/-! ### §2. Unpacking a reduction -/

namespace PolyManyOneReduction

variable {ι κ : Type} {P : RHProblem ι} {Q : RHProblem κ}
variable (R : PolyManyOneReduction P Q)

theorem solves_iff (x : ι) :
    Solves P x ↔ ∃ y, Solves R.map (x, y) ∧ Solves Q y :=
  R.correct x

theorem solves_to_exists (x : ι) :
    Solves P x → ∃ y, Solves R.map (x, y) ∧ Solves Q y := by
  intro hx
  exact (R.correct x).1 hx

theorem exists_to_solves (x : ι) :
    (∃ y, Solves R.map (x, y) ∧ Solves Q y) → Solves P x := by
  intro h
  exact (R.correct x).2 h

/-- The map relation has a unique output for each input (from total + functional). -/
theorem map_existsUnique (x : ι) : ∃! y, Solves R.map (x, y) := by
  rcases R.total x with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  intro y' hy'
  exact (R.functional x y y' hy hy').symm

/-- Size bound consequence, usable once you have a map witness. -/
theorem output_size_le (x : ι) (y : κ) (hmap : Solves R.map (x, y)) :
    Q.size y ≤ R.sizeBound (P.size x) :=
  R.size_ok x y hmap

/-- Size bound for the map-instance itself (purely structural). -/
theorem map_size_le (x : ι) (y : κ) :
    R.map.size (x, y) ≤ R.map_sizeBound (P.size x + Q.size y) :=
  R.map_size_ok x y

end PolyManyOneReduction

/-! ### §3. Interfaces for "hard" meta-lemmas (plug in later) -/

/-- Interface: composition of reductions is available once you provide a builder. -/
class ReductionComposable {ι κ ρ : Type}
    (P : RHProblem ι) (Q : RHProblem κ) (R : RHProblem ρ) where
  comp : PolyManyOneReduction P Q → PolyManyOneReduction Q R → PolyManyOneReduction P R

/-- If you have a `ReductionComposable` instance, `≤ₚ` is transitive. -/
theorem reduce_trans
    {ι κ ρ : Type} {P : RHProblem ι} {Q : RHProblem κ} {R : RHProblem ρ}
    [ReductionComposable P Q R] :
    (P ≤ₚ Q) → (Q ≤ₚ R) → (P ≤ₚ R) := by
  intro hPQ hQR
  rcases hPQ with ⟨rPQ, _⟩
  rcases hQR with ⟨rQR, _⟩
  refine ⟨ReductionComposable.comp rPQ rQR, trivial⟩

/-- Interface: NP transport along reductions (needs concrete witness/encoding machinery). -/
class NPTransportable {ι κ : Type} (P : RHProblem ι) (Q : RHProblem κ) where
  liftNP : PolyManyOneReduction P Q → NP_RH Q → NP_RH P

/-- If you have an `NPTransportable` instance, NP is closed under `≤ₚ`. -/
theorem NP_of_reduces
    {ι κ : Type} {P : RHProblem ι} {Q : RHProblem κ}
    [NPTransportable P Q] :
    (P ≤ₚ Q) → NP_RH Q → NP_RH P := by
  intro hPQ hNP
  rcases hPQ with ⟨rPQ, _⟩
  exact NPTransportable.liftNP rPQ hNP

end RevHalt.Dynamics.Operative.P_NP.ReductionLibrary
