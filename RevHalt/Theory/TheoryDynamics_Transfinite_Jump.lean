import RevHalt.Theory.TheoryDynamics_Transfinite

/-!
# RevHalt.Theory.TheoryDynamics_Transfinite_Jump

Limit operators with explicit "jump" content at limits.
This isolates the novelty injection semantics from the core transfinite dynamics.
-/

namespace RevHalt

open Set
open Ordinal

section JumpLimit

universe u v

variable {PropT : Type u}

/-- Prelimit aggregate (union over stages). -/
def preLimit {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) : Set PropT :=
  transUnionFamily (α := alpha) chain

/-- Membership characterization for `preLimit`. -/
theorem mem_preLimit_iff {alpha : Ordinal.{v}}
    (chain : ∀ beta < alpha, Set PropT) (p : PropT) :
    p ∈ preLimit (PropT := PropT) (alpha := alpha) chain
      ↔ ∃ beta, ∃ h : beta < alpha, p ∈ chain beta h := by
  rfl

/-- Each stage embeds into the prelimit aggregate. -/
theorem stage_subset_preLimit {alpha : Ordinal.{v}}
    (chain : ∀ beta < alpha, Set PropT) {beta : Ordinal.{v}} (h : beta < alpha) :
    chain beta h ⊆ preLimit (PropT := PropT) (alpha := alpha) chain := by
  intro p hp
  exact ⟨beta, h, hp⟩

/--
Limit operator built from a prelimit aggregate, a jump `J`, and a closure `Cn`.
This models "novel content injection" at limits.
-/
def jumpLimitOp (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT) : LimitOp PropT :=
  { apply := fun {alpha} chain =>
      let U := preLimit (PropT := PropT) (alpha := alpha) chain
      Cn (U ∪ J U) }

@[simp] theorem jumpLimitOp_apply
    (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT)
    {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) :
    (jumpLimitOp (PropT := PropT) Cn J).apply (alpha := alpha) chain =
      Cn (preLimit (PropT := PropT) (alpha := alpha) chain ∪
          J (preLimit (PropT := PropT) (alpha := alpha) chain)) := by
  rfl

/-- `ContinuousAtL` specialized to `jumpLimitOp`. -/
@[simp] theorem continuousAtL_jumpLimitOp
    (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT)
    (F : Set PropT → Set PropT) (A0 : Set PropT) (lim : Ordinal.{v}) :
    ContinuousAtL (PropT := PropT) (L := jumpLimitOp (PropT := PropT) Cn J) F A0 lim
      ↔ F (transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 lim) =
          Cn (preLimit (PropT := PropT) (alpha := lim)
                (fun beta (_ : beta < lim) =>
                  F (transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 beta)) ∪
              J (preLimit (PropT := PropT) (alpha := lim)
                (fun beta (_ : beta < lim) =>
                  F (transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 beta)))) := by
  rfl

/-- There exists a genuine novelty injected by `J`. -/
def InjectsNew (J : Set PropT → Set PropT) : Prop :=
  ∃ U, ∃ p, p ∈ J U ∧ p ∉ U

/-- `J` adds at least one genuinely new element to every `U`. -/
def StrictlyExtends (J : Set PropT → Set PropT) : Prop :=
  ∀ U : Set PropT, ∃ p : PropT, p ∈ J U ∧ p ∉ U

theorem StrictlyExtends.injectsNew {J : Set PropT → Set PropT}
    (h : StrictlyExtends (PropT := PropT) J) : InjectsNew (PropT := PropT) J := by
  rcases h ∅ with ⟨p, hpJ, hpNot⟩
  exact ⟨∅, p, hpJ, hpNot⟩

theorem preLimit_subset_jumpLimit_apply
    (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT)
    (hCnExt : CnExtensive (PropT := PropT) Cn)
    {alpha : Ordinal.{v}} (chain : ∀ beta < alpha, Set PropT) :
    preLimit (PropT := PropT) (alpha := alpha) chain
      ⊆ (jumpLimitOp (PropT := PropT) Cn J).apply (alpha := alpha) chain := by
  intro p hp
  have : p ∈ (preLimit (PropT := PropT) (alpha := alpha) chain ∪
      J (preLimit (PropT := PropT) (alpha := alpha) chain)) := by
    exact Or.inl hp
  exact hCnExt _ this

/-- Stage inclusion at limits for `jumpLimitOp`, assuming `Cn` is extensive. -/
theorem limitIncludesStages_jumpLimitOp
    (Cn : Set PropT → Set PropT) (J : Set PropT → Set PropT)
    (hCnExt : CnExtensive (PropT := PropT) Cn)
    (F : Set PropT → Set PropT) (A0 : Set PropT) :
    LimitIncludesStages (PropT := PropT) (jumpLimitOp (PropT := PropT) Cn J) F A0 := by
  intro lim hLim beta hbeta p hp
  have hIterEq :
      transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 lim =
        (jumpLimitOp (PropT := PropT) Cn J).apply (alpha := lim)
          (fun gamma (_ : gamma < lim) =>
            transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 gamma) := by
    simpa using
      (transIterL_limit
        (L := jumpLimitOp (PropT := PropT) Cn J)
        (F := F) (A0 := A0) (lim := lim) hLim)
  let chain : ∀ gamma < lim, Set PropT :=
    fun gamma _ => transIterL (jumpLimitOp (PropT := PropT) Cn J) F A0 gamma
  have h1 : chain beta hbeta ⊆ preLimit (PropT := PropT) (alpha := lim) chain :=
    stage_subset_preLimit (PropT := PropT) (alpha := lim) chain hbeta
  have h2 :
      preLimit (PropT := PropT) (alpha := lim) chain
        ⊆ (jumpLimitOp (PropT := PropT) Cn J).apply (alpha := lim) chain :=
    preLimit_subset_jumpLimit_apply (PropT := PropT)
      (Cn := Cn) (J := J) hCnExt (alpha := lim) chain
  have : p ∈ (jumpLimitOp (PropT := PropT) Cn J).apply (alpha := lim) chain :=
    h2 (h1 hp)
  simpa [chain] using (hIterEq.symm ▸ this)

/--
There is an element injected only at the limit, not at any stage.
This is a sharp emergence condition for the jump `J`.
-/
def JumpDiscontinuous (J : Set PropT → Set PropT) : Prop :=
  ∃ (alpha : Ordinal.{v}) (chain : ∀ beta < alpha, Set PropT),
    let U := preLimit (PropT := PropT) (alpha := alpha) chain
    ∃ p, p ∈ J U ∧ (∀ beta (h : beta < alpha), p ∉ J (chain beta h))

/--
There is a limit `lim` and a point injected from the prelimit of the iteration,
but not injected at any stage.
-/
def JumpDiscontinuousAlong
    (J : Set PropT → Set PropT)
    (L : LimitOp PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT) : Prop :=
  ∃ (lim : Ordinal.{v}) (_hLim : Order.IsSuccLimit lim),
    let U := preLimit (PropT := PropT) (alpha := lim)
      (fun beta (_ : beta < lim) => transIterL L F A0 beta)
    ∃ p : PropT, p ∈ J U ∧
      (∀ beta (_h : beta < lim), p ∉ J (transIterL L F A0 beta))

/--
A sharp emergence witness: injected at the limit, not already in the prelimit,
and not injected at any stage.
-/
def JumpEmergenceAlong
    (J : Set PropT → Set PropT)
    (L : LimitOp PropT)
    (F : Set PropT → Set PropT)
    (A0 : Set PropT) : Prop :=
  ∃ (lim : Ordinal.{v}) (_hLim : Order.IsSuccLimit lim),
    let U := preLimit (PropT := PropT) (alpha := lim)
      (fun beta (_ : beta < lim) => transIterL L F A0 beta)
    ∃ p : PropT,
      p ∈ J U ∧ p ∉ U ∧
      (∀ beta (_h : beta < lim), p ∉ J (transIterL L F A0 beta))

def MonotoneSetOp (T : Type u) (G : Set T → Set T) : Prop :=
  ∀ ⦃U V : Set T⦄, U ⊆ V → G U ⊆ G V

theorem preLimit_mono {alpha : Ordinal.{v}}
    (chain₁ chain₂ : ∀ beta < alpha, Set PropT)
    (h : ∀ beta (hb : beta < alpha), chain₁ beta hb ⊆ chain₂ beta hb) :
    preLimit (PropT := PropT) (alpha := alpha) chain₁
      ⊆ preLimit (PropT := PropT) (alpha := alpha) chain₂ := by
  intro p hp
  rcases hp with ⟨beta, hb, hp⟩
  exact ⟨beta, hb, h beta hb hp⟩

end JumpLimit

end RevHalt
