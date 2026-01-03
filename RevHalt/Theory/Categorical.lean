import RevHalt.Base.Trace
import RevHalt.Theory.Canonicity
import Mathlib.CategoryTheory.Thin

import Mathlib.Data.Set.Basic
import Mathlib.Data.ULift
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Monotone.Basic

/-!
# RevHalt.Theory.Categorical

Order- and category-theoretic structure already present in RevHalt:

1. `up` is the reflection of an arbitrary trace into the class of monotone traces:
   for monotone `X`, `up T ≤ X ↔ T ≤ X` (adjunction in a thin category / poset).

2. `ModE` / `ThE` form a Galois-style adjunction (thin category view),
   and `CloE = ThE ∘ ModE` is a closure operator (extensive, monotone, idempotent).
-/

namespace RevHalt

-- =====================================================================================
-- Pointwise order on traces
-- =====================================================================================

/-- Pointwise implication order on traces: `T ≤ U` means `∀ n, T n → U n`. -/
instance : LE Trace := ⟨fun T U => ∀ n : ℕ, T n → U n⟩

-- =====================================================================================
-- 1) `up` as a reflector / closure operator on traces (thin category view)
-- =====================================================================================

theorem le_up (T : Trace) : T ≤ up T := by
  intro n hn
  exact ⟨n, Nat.le_refl n, hn⟩

/-- `up` is monotone w.r.t. the pointwise order on traces. -/
theorem up_mono_order {T U : Trace} (h : T ≤ U) : up T ≤ up U := by
  intro n hn
  rcases hn with ⟨k, hk_le, hkT⟩
  exact ⟨k, hk_le, h k hkT⟩

/--
Reflection law: for monotone `X`, `up T ≤ X ↔ T ≤ X`.
-/
theorem up_le_iff {T X : Trace} (hX : Monotone X) :
    up T ≤ X ↔ T ≤ X := by
  constructor
  · intro hup n hn
    have : up T n := ⟨n, Nat.le_refl n, hn⟩
    exact hup n this
  · intro hTX n hn
    rcases hn with ⟨k, hk_le, hkT⟩
    have hXk : X k := hTX k hkT
    have hkn : X k → X n := hX hk_le
    exact hkn hXk

/-- `up (up T) ≤ up T`. -/
theorem up_idem_le (T : Trace) : up (up T) ≤ up T := by
  intro n hn
  rcases hn with ⟨k, hk_le, hk_up⟩
  rcases hk_up with ⟨j, hj_le, hjT⟩
  exact ⟨j, Nat.le_trans hj_le hk_le, hjT⟩

/-- `up T ≤ up (up T)`. -/
theorem le_up_idem (T : Trace) : up T ≤ up (up T) := by
  intro n hn
  rcases hn with ⟨k, hk_le, hkT⟩
  have : up T k := ⟨k, Nat.le_refl k, hkT⟩
  exact ⟨k, hk_le, this⟩

/-- Idempotence as equality of traces. -/
theorem up_idem (T : Trace) : up (up T) = up T := by
  funext n
  apply propext
  constructor
  · exact (up_idem_le (T := T)) n
  · exact (le_up_idem (T := T)) n



-- =====================================================================================
-- 1.5) Stabilization as Partial Order Bottom
-- =====================================================================================

/-- The bottom trace (constantly false). -/
def BotTrace : Trace := fun _ => False

instance : Bot Trace := ⟨BotTrace⟩

@[simp] lemma bot_trace_apply (n : ℕ) : (⊥ : Trace) n = False := rfl

/-- `up` preserves bottom. -/
theorem up_bot : up ⊥ = ⊥ := by
  funext n
  apply propext
  constructor
  · intro h
    rcases h with ⟨k, _, hk⟩
    exact hk
  · intro h
    exact False.elim h

/--
  **Algebraic Stabilization (The Operative Core)**:
  Standard theory defines stabilization logically (`∀ n, ¬ T n`).
  RevHalt defines it operatively via the `up` closure (`up T = ⊥`).

  The novelty is the operator `up` itself: it acts as a **Projector** / **Filter**.
  - If `T` contains any signal (Halt), `up T` imposes `True` (eventually).
  - If `T` stabilizes (No Halt), `up T` collapses to `⊥`.

  This makes Stabilization a **structural nullity** detected by the operator,
  rather than just a logical negation.
-/
theorem up_eq_bot_iff (T : Trace) :
    up T = ⊥ ↔ ∀ n, ¬ T n := by
  constructor
  · intro h n hn
    have hT : T ≤ up T := le_up T
    have hBot : up T n := hT n hn
    rw [h] at hBot
    exact hBot
  · intro h
    funext n
    apply propext
    constructor
    · intro hUp
      rcases hUp with ⟨k, _, hk⟩
      exact h k hk
    · intro hBot
      exact False.elim hBot

-- =====================================================================================
-- 2) `ModE` / `ThE` / `CloE` as Galois-style structure; `CloE` is a closure operator
-- =====================================================================================

section Semantics

variable {Sentence : Type}
variable {Model : Type}
variable (Sat : Model → Sentence → Prop)

theorem ModE_ThE_iff (Γ : Set Sentence) (K_models : Set Model) :
    K_models ⊆ ModE Sat Γ ↔ Γ ⊆ ThE Sat K_models := by
  constructor
  · intro hKM φ hφ M hM
    have hM' : M ∈ ModE Sat Γ := hKM hM
    exact hM' φ hφ
  · intro hΓ M hM φ hφ
    have hφ' : φ ∈ ThE Sat K_models := hΓ hφ
    exact hφ' M hM

theorem subset_CloE (Γ : Set Sentence) : Γ ⊆ CloE Sat Γ := by
  intro φ hφ M hM
  exact hM φ hφ

theorem CloE_monotone {Γ Δ : Set Sentence} (h : Γ ⊆ Δ) :
    CloE Sat Γ ⊆ CloE Sat Δ := by
  intro φ hφ M hMΔ
  have hMΓ : M ∈ ModE Sat Γ := by
    intro ψ hψ
    exact hMΔ ψ (h hψ)
  exact hφ M hMΓ

theorem ModE_CloE_eq (Γ : Set Sentence) :
    ModE Sat (CloE Sat Γ) = ModE Sat Γ := by
  ext M
  constructor
  · intro hMClo φ hφ
    have : φ ∈ CloE Sat Γ := subset_CloE (Sat := Sat) Γ hφ
    exact hMClo φ this
  · intro hMΓ φ hφ
    exact hφ M hMΓ

theorem CloE_idem (Γ : Set Sentence) :
    CloE Sat (CloE Sat Γ) = CloE Sat Γ := by
  have h : ModE Sat (CloE Sat Γ) = ModE Sat Γ := ModE_CloE_eq (Sat := Sat) Γ
  show ThE Sat (ModE Sat (CloE Sat Γ)) = CloE Sat Γ
  rw [h]
  rfl

end Semantics


-- =====================================================================================
-- 1.6) Operative Projector Proofs (The "Filter" Demonstration)
-- =====================================================================================

/--
  **Theorem: `up` is a Projector/Filter**.
  This theorem bundles the three properties that demonstrate the operative nature:
  1. **Idempotence**: Applying it twice changes nothing (Projector).
  2. **Signal Preservation**: If there is a signal (Halts), it survives.
  3. **Noise Annihilation**: If there is no signal (Stabilizes), it collapses to Bot.
-/
theorem up_is_projector (T : Trace) :
    (up (up T) = up T) ∧                  -- Idempotence
    ((∃ n, up T n) ↔ (∃ n, T n)) ∧        -- Signal Preservation
    (up T = ⊥ ↔ ∀ n, ¬ T n) :=            -- Noise Annihilation (Kernel)
by
  refine ⟨?_, ?_, ?_⟩
  · exact up_idem T
  · exact exists_up_iff T
  · exact up_eq_bot_iff T

-- =====================================================================================
-- 3) Frontier Anti-Monotonicity (Divergence under Extension)
-- =====================================================================================

section Frontier

variable {PropT : Type}
variable (Provable : Set PropT → PropT → Prop)
variable (Truth : PropT → Prop)

/--
  **Frontier (S1)**: The set of true statements not provable in a given theory S2.
  S1(S2) = { p | Truth p ∧ ¬ Provable S2 p }
-/
def Frontier (S2 : Set PropT) : Set PropT :=
  { p | Truth p ∧ ¬ Provable S2 p }

/--
  **Provable Monotonicity**: Extending a theory can only add provable statements.
  This is the standard weakening/monotonicity property of logical systems.
-/
def ProvableMonotone : Prop :=
  ∀ S S' : Set PropT, S ⊆ S' → ∀ p : PropT, Provable S p → Provable S' p

/--
  **Frontier Anti-Monotonicity**:
  If Provable is monotone, then S1 (Frontier) is anti-monotone:
  S2 ⊆ S2' → Frontier(S2') ⊆ Frontier(S2)

  More provable ⟹ smaller frontier.
  (Note: divergent bases lead to incomparable frontiers only when
  explicit witnesses exist; see `frontiers_incomparable`.)
-/
theorem frontier_anti_monotone (hMono : ProvableMonotone Provable) :
    ∀ S2 S2' : Set PropT, S2 ⊆ S2' →
      Frontier Provable Truth S2' ⊆ Frontier Provable Truth S2 := by
  intro S2 S2' hSub p hp
  unfold Frontier at hp ⊢
  constructor
  · exact hp.1
  · intro hProv
    have hProv' : Provable S2' p := hMono S2 S2' hSub p hProv
    exact hp.2 hProv'

/--
  **Frontier Divergence Witness**:
  If p is true, provable in S2_A but NOT provable in S2_B,
  then p belongs to S1(B) but not S1(A).

  This is the *sufficient condition* for frontier divergence:
  you need an explicit witness, not just incomparability of bases.
-/
theorem frontier_divergence_witness
    (S2_A S2_B : Set PropT)
    (p : PropT)
    (hp_true : Truth p)
    (hp_prov_A : Provable S2_A p)
    (hp_nprov_B : ¬ Provable S2_B p) :
    p ∈ Frontier Provable Truth S2_B ∧ p ∉ Frontier Provable Truth S2_A := by
  constructor
  · -- p ∈ Frontier(S2_B)
    unfold Frontier
    exact ⟨hp_true, hp_nprov_B⟩
  · -- p ∉ Frontier(S2_A)
    unfold Frontier
    intro ⟨_, hp_nprov_A⟩
    exact hp_nprov_A hp_prov_A

/--
  **Mutual Divergence**:
  If there exist witnesses in both directions (A proves something B doesn't,
  and B proves something A doesn't), then the frontiers are genuinely incomparable.
-/
theorem frontiers_incomparable
    (S2_A S2_B : Set PropT)
    (p q : PropT)
    (hp_true : Truth p) (hq_true : Truth q)
    (hp_prov_A : Provable S2_A p) (hp_nprov_B : ¬ Provable S2_B p)
    (hq_prov_B : Provable S2_B q) (hq_nprov_A : ¬ Provable S2_A q) :
    ¬ (Frontier Provable Truth S2_A ⊆ Frontier Provable Truth S2_B) ∧
    ¬ (Frontier Provable Truth S2_B ⊆ Frontier Provable Truth S2_A) := by
  constructor
  · -- S1(A) ⊄ S1(B) : q witnesses this
    intro hSub
    have hq_in_A : q ∈ Frontier Provable Truth S2_A := ⟨hq_true, hq_nprov_A⟩
    have hq_in_B : q ∈ Frontier Provable Truth S2_B := hSub hq_in_A
    exact hq_in_B.2 hq_prov_B
  · -- S1(B) ⊄ S1(A) : p witnesses this
    intro hSub
    have hp_in_B : p ∈ Frontier Provable Truth S2_B := ⟨hp_true, hp_nprov_B⟩
    have hp_in_A : p ∈ Frontier Provable Truth S2_A := hSub hp_in_B
    exact hp_in_A.2 hp_prov_A

end Frontier

end RevHalt

-- Axiom checks (auto):
#print axioms RevHalt.le_up
#print axioms RevHalt.up_mono_order
#print axioms RevHalt.up_le_iff
#print axioms RevHalt.up_idem_le
#print axioms RevHalt.le_up_idem
#print axioms RevHalt.up_idem
#print axioms RevHalt.bot_trace_apply
#print axioms RevHalt.up_bot
#print axioms RevHalt.up_eq_bot_iff
#print axioms RevHalt.ModE_ThE_iff
#print axioms RevHalt.subset_CloE
#print axioms RevHalt.CloE_monotone
#print axioms RevHalt.ModE_CloE_eq
#print axioms RevHalt.CloE_idem
#print axioms RevHalt.up_is_projector
#print axioms RevHalt.frontier_anti_monotone
#print axioms RevHalt.frontier_divergence_witness
#print axioms RevHalt.frontiers_incomparable

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART II: CATEGORICAL STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
# Complete Categorical Formalization

This section provides the full categorical structure of RevHalt:

1. **Category of Traces** (thin category / preorder)
2. **`up` as Closure Operator** (extensive, monotone, idempotent)
3. **Category of Sound Sets** (chain-compatible extensions)
4. **Chain as Monotone Sequence** (ℕ → SoundSet)
5. **Limit as Colimit** (universal property)

## The Key Insight

RevHalt's dynamics works because:
- `up` is a **closure operator** (monad on traces)
- The limit is a **colimit** (canonical extension)
- Extensions form a **category** (with sound inclusions as morphisms)
- The dichotomy is the **kernel characterization** (`up T = ⊥`)
-/

namespace RevHalt.Categorical

open Set
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) CATEGORY OF TRACES (Thin Category / Preorder)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Trace as a Type for categorical treatment. -/
abbrev TraceObj := RevHalt.Trace

/-- Hom-set in the trace category: T → U means T ≤ U pointwise.
    This is a thin category (at most one morphism between objects). -/
def TraceHom (T U : TraceObj) : Prop := ∀ n, T n → U n

theorem TraceHom.refl (T : TraceObj) : TraceHom T T := fun _ h => h

theorem TraceHom.trans {T U V : TraceObj} (hTU : TraceHom T U) (hUV : TraceHom U V) :
    TraceHom T V := fun n hT => hUV n (hTU n hT)

-- ----------------------------------------------------------------------------
-- 1.1) TraceObj as a genuine `CategoryTheory.Category`
-- ----------------------------------------------------------------------------

instance : CategoryStruct TraceObj where
  Hom T U := ULift (PLift (TraceHom T U))
  id T := ⟨⟨TraceHom.refl T⟩⟩
  comp f g := ⟨⟨TraceHom.trans f.down.down g.down.down⟩⟩

instance (T U : TraceObj) : Subsingleton (T ⟶ U) :=
  ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin TraceObj := fun _ _ => by
  infer_instance

instance : Category TraceObj := CategoryTheory.thin_category

/-- Convert a Prop-level `TraceHom` into a categorical morphism. -/
def homOfTraceHom {T U : TraceObj} (h : TraceHom T U) : T ⟶ U :=
  ULift.up (PLift.up h)

/-- Extract the underlying `TraceHom` from a categorical morphism. -/
def traceHomOfHom {T U : TraceObj} (f : T ⟶ U) : TraceHom T U :=
  f.down.down

@[simp] theorem traceHomOfHom_homOfTraceHom {T U : TraceObj} (h : TraceHom T U) :
    traceHomOfHom (homOfTraceHom h) = h :=
  rfl

@[simp] theorem homOfTraceHom_traceHomOfHom {T U : TraceObj} (f : T ⟶ U) :
    homOfTraceHom (traceHomOfHom f) = f := by
  apply Subsingleton.elim

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) `up` AS CLOSURE OPERATOR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The `up` operator as a function on TraceObj. -/
def upOp : TraceObj → TraceObj := RevHalt.up

/-- Extensive: T ≤ up T -/
theorem upOp_extensive (T : TraceObj) : TraceHom T (upOp T) := RevHalt.le_up T

/-- Monotone: T ≤ U → up T ≤ up U -/
theorem upOp_monotone {T U : TraceObj} (h : TraceHom T U) : TraceHom (upOp T) (upOp U) :=
  RevHalt.up_mono_order h

/-- Idempotent: up (up T) = up T -/
theorem upOp_idempotent (T : TraceObj) : upOp (upOp T) = upOp T :=
  RevHalt.up_idem T

/-- Closure bundle. -/
structure ClosureOperator (α : Type) where
  cl : α → α
  hom : α → α → Prop
  extensive : ∀ a, hom a (cl a)
  monotone : ∀ {a b}, hom a b → hom (cl a) (cl b)
  idempotent : ∀ a, cl (cl a) = cl a

/-- `up` is a closure operator on TraceObj. -/
def upClosure : ClosureOperator TraceObj where
  cl := upOp
  hom := TraceHom
  extensive := upOp_extensive
  monotone := @upOp_monotone
  idempotent := upOp_idempotent

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) CATEGORY OF SOUND SETS
-- ═══════════════════════════════════════════════════════════════════════════════

variable {PropT : Type} (Truth : PropT → Prop)

/-- A sound set: a set with proof of soundness. -/
structure SoundSet where
  carrier : Set PropT
  sound : ∀ p ∈ carrier, Truth p

/-- Morphisms between sound sets: inclusions. -/
def SoundSetHom (S T : SoundSet Truth) : Prop := S.carrier ⊆ T.carrier

theorem SoundSetHom.refl (S : SoundSet Truth) : SoundSetHom Truth S S := Set.Subset.refl _

theorem SoundSetHom.trans {S T U : SoundSet Truth} (hST : SoundSetHom Truth S T)
    (hTU : SoundSetHom Truth T U) : SoundSetHom Truth S U := Set.Subset.trans hST hTU

-- ----------------------------------------------------------------------------
-- 3.1) SoundSet as a genuine `CategoryTheory.Category`
-- ----------------------------------------------------------------------------

instance : CategoryStruct (SoundSet Truth) where
  Hom S T := ULift (PLift (SoundSetHom Truth S T))
  id S := ⟨⟨SoundSetHom.refl (Truth := Truth) S⟩⟩
  comp f g := ⟨⟨SoundSetHom.trans (Truth := Truth) f.down.down g.down.down⟩⟩

instance (S T : SoundSet Truth) : Subsingleton (S ⟶ T) :=
  ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin (SoundSet Truth) := fun _ _ => by
  infer_instance

instance : Category (SoundSet Truth) := CategoryTheory.thin_category

/-- Convert a Prop-level inclusion `SoundSetHom` into a categorical morphism. -/
def homOfSoundSetHom {S T : SoundSet Truth} (h : SoundSetHom Truth S T) : S ⟶ T :=
  ULift.up (PLift.up h)

/-- Extract the underlying inclusion from a categorical morphism. -/
def soundSetHomOfHom {S T : SoundSet Truth} (f : S ⟶ T) : SoundSetHom Truth S T :=
  f.down.down

@[simp] theorem soundSetHomOfHom_homOfSoundSetHom {S T : SoundSet Truth} (h : SoundSetHom Truth S T) :
    soundSetHomOfHom (Truth := Truth) (homOfSoundSetHom (Truth := Truth) h) = h :=
  rfl

@[simp] theorem homOfSoundSetHom_soundSetHomOfHom {S T : SoundSet Truth} (f : S ⟶ T) :
    homOfSoundSetHom (Truth := Truth) (soundSetHomOfHom (Truth := Truth) f) = f := by
  apply Subsingleton.elim

/-- Sound sets are extensional by their carrier (soundness proof is Prop). -/
@[ext] theorem SoundSet.ext {S T : SoundSet Truth} (h : S.carrier = T.carrier) : S = T := by
  cases S with
  | mk SCarrier SSnd =>
    cases T with
    | mk TCarrier TSnd =>
      cases h
      have : SSnd = TSnd := by
        apply Subsingleton.elim
      cases this
      rfl

instance : LE (SoundSet Truth) := ⟨SoundSetHom Truth⟩

instance : PartialOrder (SoundSet Truth) where
  le := (· ≤ ·)
  le_refl S := SoundSetHom.refl (Truth := Truth) S
  le_trans _ _ _ := SoundSetHom.trans (Truth := Truth)
  le_antisymm S T hST hTS := by
    apply SoundSet.ext (Truth := Truth)
    ext p
    exact Iff.intro (fun hp => hST hp) (fun hp => hTS hp)


/-- The empty sound set (initial object). -/
def SoundSet.empty : SoundSet Truth where
  carrier := ∅
  sound := fun _ h => False.elim h

/-- Empty is initial. -/
theorem SoundSet.empty_initial (S : SoundSet Truth) : SoundSetHom Truth (SoundSet.empty Truth) S :=
  Set.empty_subset _

/-- Top sound set: all true propositions. -/
def SoundSet.top : SoundSet Truth where
  carrier := {p | Truth p}
  sound := by
    intro p hp
    simpa using hp

/-- Binary sup on sound sets: union of carriers. -/
def SoundSet.sup (S T : SoundSet Truth) : SoundSet Truth where
  carrier := S.carrier ∪ T.carrier
  sound := by
    intro p hp
    rcases hp with hp | hp
    · exact S.sound p hp
    · exact T.sound p hp

/-- Binary inf on sound sets: intersection of carriers. -/
def SoundSet.inf (S T : SoundSet Truth) : SoundSet Truth where
  carrier := S.carrier ∩ T.carrier
  sound := by
    intro p hp
    exact S.sound p hp.1

instance : CompleteLattice (SoundSet Truth) where
  le := (· ≤ ·)
  le_refl S := SoundSetHom.refl (Truth := Truth) S
  le_trans _ _ _ := SoundSetHom.trans (Truth := Truth)
  le_antisymm S T hST hTS := by
    apply SoundSet.ext (Truth := Truth)
    ext p
    exact Iff.intro (fun hp => hST hp) (fun hp => hTS hp)
  sup := SoundSet.sup (Truth := Truth)
  le_sup_left S T := by
    intro p hp
    exact Or.inl hp
  le_sup_right S T := by
    intro p hp
    exact Or.inr hp
  sup_le S T U hSU hTU := by
    intro p hp
    rcases hp with hp | hp
    · exact hSU hp
    · exact hTU hp
  inf := SoundSet.inf (Truth := Truth)
  inf_le_left S T := by
    intro p hp
    exact hp.1
  inf_le_right S T := by
    intro p hp
    exact hp.2
  le_inf S T U hST hSU := by
    intro p hp
    exact ⟨hST hp, hSU hp⟩
  top := SoundSet.top Truth
  le_top S := by
    intro p hp
    exact S.sound p hp
  bot := SoundSet.empty Truth
  bot_le S := by
    intro p hp
    exact False.elim hp
  sSup K :=
    { carrier := {p | ∃ S, S ∈ K ∧ p ∈ S.carrier}
      sound := by
        intro p hp
        rcases hp with ⟨S, _hSK, hpS⟩
        exact S.sound p hpS }
  le_sSup K S hS := by
    intro p hp
    exact ⟨S, hS, hp⟩
  sSup_le K S h := by
    intro p hp
    rcases hp with ⟨T, hTK, hpT⟩
    exact h T hTK hpT
  sInf K :=
    { carrier := {p | Truth p ∧ ∀ S, S ∈ K → p ∈ S.carrier}
      sound := by
        intro p hp
        exact hp.1 }
  le_sInf K S h := by
    intro p hp
    refine ⟨S.sound p hp, ?_⟩
    intro T hTK
    exact h T hTK hp
  sInf_le K S hS := by
    intro p hp
    exact hp.2 S hS

/-- Step: extend by adding a true element. -/
def SoundSet.step (S : SoundSet Truth) (p : PropT) (hp : Truth p) : SoundSet Truth where
  carrier := S.carrier ∪ {p}
  sound := by
    intro q hq
    cases hq with
    | inl h => exact S.sound q h
    | inr h => rw [h]; exact hp

/-- Step is monotone (S ≤ step S p). -/
theorem SoundSet.le_step (S : SoundSet Truth) (p : PropT) (hp : Truth p) :
    SoundSetHom Truth S (S.step Truth p hp) := Set.subset_union_left

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) CHAIN AND LIMIT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A chain is a monotone sequence of SoundSets. -/
structure SoundChain where
  seq : ℕ → SoundSet Truth
  mono : ∀ n, SoundSetHom Truth (seq n) (seq (n + 1))

/-- The limit of a chain: union of all stages. -/
def SoundChain.lim (C : SoundChain Truth) : SoundSet Truth where
  carrier := { p | ∃ n, p ∈ (C.seq n).carrier }
  sound p hp := by
    obtain ⟨n, hn⟩ := hp
    exact (C.seq n).sound p hn

/-- The limit is the supremum of the chain (viewed as a set via `range`). -/
theorem SoundChain.lim_eq_sSup_range (C : SoundChain Truth) :
    C.lim Truth = sSup (Set.range C.seq) := by
  apply SoundSet.ext (Truth := Truth)
  ext p
  constructor
  · intro hp
    rcases hp with ⟨n, hn⟩
    refine ⟨C.seq n, ⟨n, rfl⟩, hn⟩
  · intro hp
    rcases hp with ⟨S, ⟨n, rfl⟩, hpS⟩
    exact ⟨n, hpS⟩

/-- Each stage embeds into the limit. -/
theorem SoundChain.seq_le_lim (C : SoundChain Truth) (n : ℕ) :
    SoundSetHom Truth (C.seq n) (C.lim Truth) := by
  intro p hp
  exact ⟨n, hp⟩

/-- Universal property of the limit (cocone mediating map). -/
theorem SoundChain.lim_universal (C : SoundChain Truth) (T : SoundSet Truth)
    (h : ∀ n, SoundSetHom Truth (C.seq n) T) :
    SoundSetHom Truth (C.lim Truth) T := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  exact h n hn

/-- Colimit Characterization: lim is the smallest containing all stages. -/
theorem SoundChain.lim_is_colimit (C : SoundChain Truth) (T : SoundSet Truth) :
    SoundSetHom Truth (C.lim Truth) T ↔ ∀ n, SoundSetHom Truth (C.seq n) T := by
  constructor
  · intro hLim n
    exact Set.Subset.trans (C.seq_le_lim Truth n) hLim
  · exact C.lim_universal Truth T

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) KERNEL CHARACTERIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The kernel of up: traces where up T = ⊥. -/
def upKernel : Set TraceObj := { T | upOp T = ⊥ }

/-- Kernel membership is equivalent to stabilization. -/
theorem mem_upKernel_iff (T : TraceObj) :
    T ∈ upKernel ↔ ∀ n, ¬ T n :=
  RevHalt.up_eq_bot_iff T

/-- The dichotomy as categorical statement (requires EM). -/
theorem trace_dichotomy_categorical (T : TraceObj)
    (em : ∀ P : Prop, P ∨ ¬P) :
    (∃ n, T n) ∨ T ∈ upKernel := by
  cases em (∃ n, T n) with
  | inl h => exact Or.inl h
  | inr h =>
    right
    rw [mem_upKernel_iff]
    intro n hn
    exact h ⟨n, hn⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) ADJUNCTION: up ⊣ inclusion
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A trace is closed (monotone / fixed by up) if up T = T. -/
def IsClosedTrace (T : TraceObj) : Prop := upOp T = T

/-- The type of closed traces. -/
def ClosedTrace := { T : TraceObj // IsClosedTrace T }

/-- up T is always closed. -/
theorem upOp_isClosed (T : TraceObj) : IsClosedTrace (upOp T) :=
  upOp_idempotent T


/-- up corestricts to closed traces. -/
def upToClosed (T : TraceObj) : ClosedTrace :=
  ⟨upOp T, upOp_isClosed T⟩

/--
**Adjunction**: `up T ≤ X (closed) ↔ T ≤ X`.

This is the universal property making `up` left adjoint to inclusion.
In categorical terms: up ⊣ inclusion.
-/
theorem up_left_adjoint (T : TraceObj) (X : ClosedTrace) :
    TraceHom (upOp T) X.val ↔ TraceHom T X.val := by
  constructor
  · intro h
    exact TraceHom.trans (upOp_extensive T) h
  · intro hTX
    have hClosed := X.property
    have hMono : Monotone X.val := by
      intro m n hmn hXm
      -- X is closed means X = up X, so X is monotone
      have hUpX : X.val = upOp X.val := by exact hClosed.symm
      rw [hUpX] at hXm ⊢
      obtain ⟨k, hk_le, hkX⟩ := hXm
      exact ⟨k, Nat.le_trans hk_le hmn, hkX⟩
    exact (RevHalt.up_le_iff hMono).mpr hTX

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) FUNCTORIALITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- up is a functor (preserves morphisms). -/
theorem upOp_functor {T U : TraceObj} (h : TraceHom T U) :
    TraceHom (upOp T) (upOp U) :=
  upOp_monotone h

/-- Chain embedding is functorial: if C ≤ D pointwise, then lim C ≤ lim D. -/
theorem SoundChain.lim_mono (C D : SoundChain Truth)
    (h : ∀ n, SoundSetHom Truth (C.seq n) (D.seq n)) :
    SoundSetHom Truth (C.lim Truth) (D.lim Truth) := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, h n hn⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) CROSS-FILE CONNECTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Connections to Other RevHalt Modules

The categorical structure connects to other files as follows:

1. **Base/Trace.lean**: `upOp = RevHalt.up`, `mem_upKernel_iff = up_eq_bot_iff`

2. **Theory/AbstractDynamics.lean**: `SoundSet` is analogous to `PickWorld.State`,
   `SoundChain` is analogous to `Chain`, `lim` is analogous to `omegaState`.

3. **Theory/RelativeFoundations.lean**: `upOp` relates to `upE` via:
   `upE Eval Γ s = RevHalt.up (EvalTrace Eval Γ s)`

4. **Theory/OrdinalBoundary.lean**: `trace_dichotomy_categorical` is the
   parametric version of `dichotomy_from_em`.

5. **Theory/RelativeR1.lean**: `CutMonotone` implies uniqueness of `k`,
   which connects to the categorical view where the window is "terminal"
   in a slice category.
-/

/-- Link to Base: upOp is RevHalt.up -/
theorem upOp_eq_up : upOp = RevHalt.up := rfl

/-- Link to Base: kernel characterization matches ¬Halts -/
theorem upKernel_eq_not_halts (T : TraceObj) :
    T ∈ upKernel ↔ ¬ RevHalt.Halts T := by
  rw [mem_upKernel_iff]
  constructor
  · intro h ⟨n, hn⟩; exact h n hn
  · intro h n hn; exact h ⟨n, hn⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Summary: The Categorical Picture

1. **TraceObj** forms a preorder category (thin category).
2. **upOp** is a closure operator (extensive, monotone, idempotent).
3. **SoundSet** forms a preorder category (sound extensions).
4. **SoundChain.lim** is the colimit (universal property: `lim_is_colimit`).
5. **Dichotomy = kernel characterization** (`trace_dichotomy_categorical`).
-/

end RevHalt.Categorical

-- Axiom checks for categorical section:
#print axioms RevHalt.Categorical.TraceHom.refl
#print axioms RevHalt.Categorical.TraceHom.trans
#print axioms RevHalt.Categorical.upOp_extensive
#print axioms RevHalt.Categorical.upOp_monotone
#print axioms RevHalt.Categorical.upOp_idempotent
#print axioms RevHalt.Categorical.upClosure
#print axioms RevHalt.Categorical.SoundSetHom.refl
#print axioms RevHalt.Categorical.SoundSetHom.trans
#print axioms RevHalt.Categorical.SoundSet.empty_initial
#print axioms RevHalt.Categorical.SoundChain.seq_le_lim
#print axioms RevHalt.Categorical.SoundChain.lim_is_colimit
#print axioms RevHalt.Categorical.mem_upKernel_iff
#print axioms RevHalt.Categorical.trace_dichotomy_categorical
