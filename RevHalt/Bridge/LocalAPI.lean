import RevHalt.Theory.Complementarity
import RevHalt.Bridge.Context
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Disjoint

namespace RevHalt

open Set

namespace LocalAPI

variable {Code PropT : Type}

/-- Local "gap" witness: true but unprovable (in the internal ctx). -/
def GapWitness (ctx : EnrichedContext Code PropT) : Type :=
  { p : PropT // ctx.Truth p ∧ ¬ ctx.Provable p }

/-- A theory is "sound" if it contains only truths (in the external Truth sense). -/
def SoundTheory (Truth : PropT → Prop) (T : Set PropT) : Prop :=
  ∀ p, p ∈ T → Truth p

/-- Pure extension by adding an axiom p. -/
def Extend (T : Set PropT) (p : PropT) : Set PropT :=
  T ∪ ({p} : Set PropT)

/-- (1) Sound extension parameterized by a witness `w : GapWitness ctx`. -/
theorem extend_sound_of_gapWitness
    (ctx : EnrichedContext Code PropT)
    (T0 : Set PropT)
    (hT0 : SoundTheory ctx.Truth T0)
    (w : GapWitness ctx) :
    T0 ⊆ Extend T0 w.1 ∧
    SoundTheory ctx.Truth (Extend T0 w.1) ∧
    w.1 ∈ Extend T0 w.1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact Or.inl hq
  · intro q hq
    rcases hq with hq | hq
    · exact hT0 q hq
    · -- q ∈ {w.1}
      have : q = w.1 := by
        simpa [Set.mem_singleton_iff] using hq
      simpa [this] using w.2.1
  · exact Or.inr (by simp)

/-- Disjunction of singletons {p} and {Not p}. -/
theorem singleton_disjoint_singleton_not
    (ctx : ComplementaritySystem Code PropT)
    (p : PropT)
    (hneq : p ≠ ctx.Not p) :
    Disjoint ({p} : Set PropT) ({ctx.Not p} : Set PropT) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hy
  have hx' : x = p := by simpa [Set.mem_singleton_iff] using hx
  have hy' : x = ctx.Not p := by simpa [Set.mem_singleton_iff] using hy
  exact hneq (hx'.symm.trans hy')

/-- "New part" of an extension (what is added beyond T0). -/
def NewPart (T0 : Set PropT) (p : PropT) : Set PropT :=
  Extend T0 p \ T0

/-- If p ∉ T0, then the new part is exactly {p}. -/
theorem newPart_eq_singleton_of_not_mem
    (T0 : Set PropT) (p : PropT) (hp : p ∉ T0) :
    NewPart T0 p = ({p} : Set PropT) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxE, hxN⟩
    rcases hxE with hxT0 | hxSing
    · exact (hxN hxT0).elim
    · exact hxSing
  · intro hx
    refine ⟨?_, ?_⟩
    · exact Or.inr hx
    · intro hxT0
      have : p ∈ T0 := by simpa [Set.mem_singleton_iff] using (show x = p from by
        simpa [Set.mem_singleton_iff] using hx) ▸ hxT0
      exact hp this

/--
(2) Disjunction of the two extensions (at the "new part" level) parameterized by `w`.

Minimal purely set-theoretic hypotheses:
- w.1 ∉ T0
- Not w.1 ∉ T0
- w.1 ≠ Not w.1
-/
theorem disjoint_newParts_of_gapWitness
    (ctx : ComplementaritySystem Code PropT)
    (T0 : Set PropT)
    (w_p : PropT)
    (h_notin : w_p ∉ T0)
    (h_notin_not : ctx.Not w_p ∉ T0)
    (hneq : w_p ≠ ctx.Not w_p) :
    Disjoint (NewPart T0 w_p) (NewPart T0 (ctx.Not w_p)) := by
  -- Reduced to {w_p} ⟂ {Not w_p}
  have h1 : NewPart T0 w_p = ({w_p} : Set PropT) :=
    newPart_eq_singleton_of_not_mem (T0 := T0) (p := w_p) h_notin
  have h2 : NewPart T0 (ctx.Not w_p) = ({ctx.Not w_p} : Set PropT) :=
    newPart_eq_singleton_of_not_mem (T0 := T0) (p := ctx.Not w_p) h_notin_not
  simpa [h1, h2] using singleton_disjoint_singleton_not (ctx := ctx) (p := w_p) hneq

end LocalAPI

end RevHalt
