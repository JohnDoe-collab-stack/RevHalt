import RevHalt.Theory.RelativeFoundations
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic


/-!
# LPO Relative to Formation Referential (R1)

This file formalizes the key missing abstraction: **LPO relative to a grammar of admissible sequences**.

## Core Insight

The standard `LPO_Eval` quantifies over **all** sequences `s : ℕ → Sentence`.
But in a referential framework, we only quantify over **admissible** sequences (those formable in R1).

This changes:
1. The logical strength of LPO (restricted LPO can be weaker)
2. The collapse condition (constant sequence trick requires `AdmitsConst`)
3. The hierarchy (more restrictive R1 → weaker LPO)

## Abstract Theory

This is abstract theory, independent of any specific dynamics.
For any dynamics that generates a restricted grammar:
- If `AdmitsConst` is FALSE, `LPO_R1` does NOT imply `EM_Eval` via the usual trick
- The hierarchy theorem relates different grammars

-/

namespace RevHalt.RelativeR1

variable {Sentence : Type}

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) LPO Relative to Grammar R1
-- ═══════════════════════════════════════════════════════════════════════════════

/-- LPO relative to a grammar of admissible sequences (R1).
    Only quantifies over sequences satisfying `Adm`. -/
def LPO_Eval_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ s, Adm s → (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))

/-- EM at evaluation level (imported from RelativeFoundations, renamed for clarity). -/
def EM_Eval (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) : Prop :=
  ∀ φ : Sentence, Eval Γ φ ∨ ¬ Eval Γ φ

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Collapse Condition: AdmitsConst
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A grammar `Adm` admits constant sequences.
    This is the condition for the "constant sequence trick" to work. -/
def AdmitsConst (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ φ, Adm (fun _ => φ)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Collapse Theorem: LPO_R1 → EM_Eval (conditional)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The constant sequence trick, but properly conditioned on R1 admitting constants.
    If R1 admits constant sequences, then LPO_R1 implies EM_Eval. -/
theorem LPO_R1_imp_EM_if_const
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop)
    (hConst : AdmitsConst Adm) :
    LPO_Eval_R1 Eval Γ Adm → EM_Eval Eval Γ := by
  intro hLPO φ
  -- The constant sequence (fun _ => φ) is admissible by hypothesis
  have hAdm : Adm (fun _ => φ) := hConst φ
  -- Apply LPO_R1 to this constant sequence
  have h := hLPO (fun _ => φ) hAdm
  cases h with
  | inl hex =>
    -- exists n, Eval Γ φ
    left
    exact hex.elim fun _ hx => hx
  | inr hall =>
    -- forall n, ¬ Eval Γ φ
    right
    exact hall 0

/-- The unconditional LPO_Eval is LPO_R1 with trivial grammar (all sequences admissible). -/
def AllAdm : (ℕ → Sentence) → Prop := fun _ => True

theorem AllAdm_admits_const : AdmitsConst (AllAdm (Sentence := Sentence)) := by
  intro _
  trivial

/-- Global LPO equals LPO_R1 with trivial grammar. -/
theorem LPO_Eval_eq_LPO_R1_All
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    RevHalt.RelativeFoundations.LPO_Eval Eval Γ ↔ LPO_Eval_R1 Eval Γ AllAdm := by
  constructor
  · intro h s _
    exact h s
  · intro h s
    exact h s trivial

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Hierarchy: Monotonicity on R1
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Monotonicity: if Adm₁ ⊆ Adm₂, then LPO on Adm₂ implies LPO on Adm₁.
    (Stronger grammar restriction → weaker LPO requirement) -/
theorem LPO_mono_R1
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm₁ Adm₂ : (ℕ → Sentence) → Prop)
    (hSub : ∀ s, Adm₁ s → Adm₂ s) :
    LPO_Eval_R1 Eval Γ Adm₂ → LPO_Eval_R1 Eval Γ Adm₁ := by
  intro h s hs1
  exact h s (hSub s hs1)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Non-Collapse: Examples of Grammars That Don't Admit Constants
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The empty grammar (no sequences admissible).
    LPO_R1 is trivially true, but gives no EM. -/
def EmptyAdm : (ℕ → Sentence) → Prop := fun _ => False

theorem LPO_R1_empty_trivial
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    LPO_Eval_R1 Eval Γ EmptyAdm := by
  intro s hs
  exact False.elim hs

theorem EmptyAdm_not_admits_const [Inhabited Sentence] :
    ¬ AdmitsConst (EmptyAdm (Sentence := Sentence)) := by
  intro h
  exact h default

/-- Changing sequences only: sequences where `s(n) ≠ s(n+1)` for all n.
    This grammar cannot admit constants. -/
def ChangingAdm (_Eval : List Sentence → Sentence → Prop) (_Γ : List Sentence)
    : (ℕ → Sentence) → Prop :=
  fun s => ∀ n, s n ≠ s (n + 1)

theorem ChangingAdm_not_admits_const [Inhabited Sentence]
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence) :
    ¬ AdmitsConst (ChangingAdm Eval Γ) := by
  intro h
  -- For any φ, the constant sequence should be in ChangingAdm
  -- But constant sequence has s(0) = s(1), contradiction
  have hConst : ChangingAdm Eval Γ (fun _ => default) := h default
  have hNeq : (fun _ => default) 0 ≠ (fun _ => default) 1 := hConst 0
  exact hNeq rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Link to Evaluative Trace Schema
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HaltsE relative to R1 -/
def HaltsE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (_Adm : (ℕ → Sentence) → Prop) (s : ℕ → Sentence) (_hAdm : _Adm s) : Prop :=
  ∃ n, Eval Γ (s n)

/-- StabilizesE relative to R1 -/
def StabilizesE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (_Adm : (ℕ → Sentence) → Prop) (s : ℕ → Sentence) (_hAdm : _Adm s) : Prop :=
  ∀ n, ¬ Eval Γ (s n)

/-- The dichotomy on admissible sequences -/
def DichotomyE_R1 (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) : Prop :=
  ∀ s, Adm s → (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))

/-- DichotomyE_R1 is exactly LPO_Eval_R1 -/
theorem DichotomyE_R1_iff_LPO_R1
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Adm : (ℕ → Sentence) → Prop) :
    DichotomyE_R1 Eval Γ Adm ↔ LPO_Eval_R1 Eval Γ Adm := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Cut/Bit directement dans R1 (sans RefSystem)
-- ═══════════════════════════════════════════════════════════════════════════════

namespace CutBit

variable {Referent : Type}

/-- Dyadique canonique (fenêtre à la profondeur n). -/
def dyad (n : ℕ) (k : ℤ) : ℚ :=
  (k : ℚ) / ((2 : ℚ) ^ n)

/-- Lien discret/continu au niveau sémantique (R2), exprimé *uniquement* avec Cut/Bit. -/
def BitCutLink (Truth : Sentence → Prop)
    (Cut : ℚ → Referent → Sentence) (Bit : ℕ → Fin 2 → Referent → Sentence) : Prop :=
  ∀ (n : ℕ) (a : Fin 2) (x : Referent),
    Truth (Bit n a x) ↔
      ∃ k : ℤ,
        Truth (Cut (dyad n k) x) ∧
        ¬ Truth (Cut (dyad n (k + 1)) x) ∧
        (k.toNat % 2) = a.val

/-- (R1) Grammaire Bit : suites de raffinements bit-indexés. -/
def AdmBit (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent) : (ℕ → Sentence) → Prop :=
  fun s => ∀ n, ∃ a : Fin 2, s n = Bit n a x

/-- (R1) Grammaire Cut dyadique : suites de coupes dyadiques. -/
def AdmCutDyadic (Cut : ℚ → Referent → Sentence) (x : Referent) : (ℕ → Sentence) → Prop :=
  fun s => ∀ n, ∃ k : ℤ, s n = Cut (dyad n k) x

/-- (R1) Grammaire mixte : even=Cut, odd=Bit (deux référentiels couplés). -/
def AdmMix (Cut : ℚ → Referent → Sentence) (Bit : ℕ → Fin 2 → Referent → Sentence)
    (x : Referent) : (ℕ → Sentence) → Prop :=
  fun s =>
    (∀ t, ∃ k : ℤ, s (2*t) = Cut (dyad t k) x) ∧
    (∀ t, ∃ a : Fin 2, s (2*t + 1) = Bit t a x)

/-- LPO_Eval relatif à la grammaire Bit (R1). -/
def LPO_Eval_Bit (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent) : Prop :=
  LPO_Eval_R1 (Sentence := Sentence) Eval Γ (AdmBit (Sentence := Sentence) (Referent := Referent) Bit x)

/-- LPO_Eval relatif à la grammaire Cut dyadique (R1). -/
def LPO_Eval_CutDyadic (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Cut : ℚ → Referent → Sentence) (x : Referent) : Prop :=
  LPO_Eval_R1 (Sentence := Sentence) Eval Γ (AdmCutDyadic (Sentence := Sentence) (Referent := Referent) Cut x)

/-- LPO_Eval relatif à la grammaire mixte Cut/Bit (R1). -/
def LPO_Eval_Mix (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Cut : ℚ → Referent → Sentence) (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent) : Prop :=
  LPO_Eval_R1 (Sentence := Sentence) Eval Γ (AdmMix (Sentence := Sentence) (Referent := Referent) Cut Bit x)

-- ─────────────────────────────────────────────────────────────────────────────
-- (A) Pointwise: du Bit (vrai) on extrait des *témoins* Cut (sans choix global).
-- ─────────────────────────────────────────────────────────────────────────────

/-- Version pointwise (0 axiome) :
si la suite `s` est Bit-admissible et chaque terme est vrai,
alors pour chaque n on obtient un k (fenêtre dyadique) témoin. -/
theorem bit_truth_to_cut_witness_pointwise
    (Truth : Sentence → Prop)
    (Cut : ℚ → Referent → Sentence) (Bit : ℕ → Fin 2 → Referent → Sentence)
    (hLink : BitCutLink (Sentence := Sentence) (Referent := Referent) Truth Cut Bit)
    (x : Referent) (s : ℕ → Sentence)
    (hAdm : AdmBit (Sentence := Sentence) (Referent := Referent) Bit x s)
    (hTrue : ∀ n, Truth (s n)) :
    ∀ n, ∃ (a : Fin 2) (k : ℤ),
      s n = Bit n a x ∧
      Truth (Cut (dyad n k) x) ∧
      ¬ Truth (Cut (dyad n (k + 1)) x) ∧
      (k.toNat % 2) = a.val := by
  intro n
  rcases hAdm n with ⟨a, hsa⟩
  have hBitTrue : Truth (Bit n a x) := by
    -- s n = Bit n a x et Truth (s n)
    simpa [hsa] using (hTrue n)
  have hWin : ∃ k : ℤ,
      Truth (Cut (dyad n k) x) ∧
      ¬ Truth (Cut (dyad n (k + 1)) x) ∧
      (k.toNat % 2) = a.val := (hLink n a x).1 hBitTrue
  rcases hWin with ⟨k, hkCut, hkNot, hkPar⟩
  exact ⟨a, k, hsa, hkCut, hkNot, hkPar⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- (B) Choix global: passer de ∀n ∃k ... à ∃f : ℕ → ℤ ...
--     (isole Classical.choice, comme tu veux).
-- ─────────────────────────────────────────────────────────────────────────────

/-- Version "sélecteur" : on fabrique une fonction k(n).
Cette étape isole exactement `Classical.choice`. -/
theorem bit_truth_to_cut_selector
    (Truth : Sentence → Prop)
    (Cut : ℚ → Referent → Sentence) (Bit : ℕ → Fin 2 → Referent → Sentence)
    (hLink : BitCutLink (Sentence := Sentence) (Referent := Referent) Truth Cut Bit)
    (x : Referent) (s : ℕ → Sentence)
    (hAdm : AdmBit (Sentence := Sentence) (Referent := Referent) Bit x s)
    (hTrue : ∀ n, Truth (s n)) :
    ∃ f : ℕ → ℤ,
      ∀ n, ∃ a : Fin 2,
        s n = Bit n a x ∧
        Truth (Cut (dyad n (f n)) x) ∧
        ¬ Truth (Cut (dyad n (f n + 1)) x) ∧
        ((f n).toNat % 2) = a.val := by
  classical
  have hPW :=
    bit_truth_to_cut_witness_pointwise (Sentence := Sentence) (Referent := Referent)
      Truth Cut Bit hLink x s hAdm hTrue
  -- Extract function f using Choice (skolemization)
  -- hPW n : ∃ a, ∃ k, ...
  -- Classical.choose gets a
  -- Classical.choose_spec gets ∃ k, ...
  -- Classical.choose of that gets k (which is our f n)
  exists (fun n => Classical.choose (Classical.choose_spec (hPW n)))
  intro n
  exists (Classical.choose (hPW n))
  exact Classical.choose_spec (Classical.choose_spec (hPW n))

-- ─────────────────────────────────────────────────────────────────────────────
-- (C) Non-collapse typique : AdmBit n’admet pas les constantes
--     dès qu’on assume la distinction des indices (optionnel mais utile).
-- ─────────────────────────────────────────────────────────────────────────────

/-- Hypothèse structurelle minimale : changer l’indice n change la formule Bit. -/
def BitIndexDistinct (Bit : ℕ → Fin 2 → Referent → Sentence) : Prop :=
  ∀ {n m : ℕ} {a b : Fin 2} {x : Referent}, n ≠ m → Bit n a x ≠ Bit m b x

/-- Sous BitIndexDistinct, la grammaire AdmBit n’admet pas les constantes.
(=> le "const trick" est bloqué par R1, exactement ce que tu veux). -/
theorem AdmBit_not_admits_const
    (Bit : ℕ → Fin 2 → Referent → Sentence)
    (hDist : BitIndexDistinct (Sentence := Sentence) (Referent := Referent) Bit)
    (x : Referent) :
    ¬ AdmitsConst (Sentence := Sentence)
        (AdmBit (Sentence := Sentence) (Referent := Referent) Bit x) := by
  intro hConst
  -- applique AdmitsConst à φ = Bit 0 0 x
  have hAdm : AdmBit (Sentence := Sentence) (Referent := Referent) Bit x (fun _ => Bit 0 (0 : Fin 2) x) :=
    hConst (Bit 0 (0 : Fin 2) x)
  -- au rang 1, il faut exister a avec Bit 0 0 x = Bit 1 a x
  rcases hAdm 1 with ⟨a1, ha1⟩
  have hEq : Bit 0 (0 : Fin 2) x = Bit 1 a1 x := by
    simpa using ha1
  have hNe : Bit 0 (0 : Fin 2) x ≠ Bit 1 a1 x := hDist (by decide)
  exact hNe hEq

end CutBit


end RevHalt.RelativeR1

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.RelativeR1.LPO_R1_imp_EM_if_const
#print axioms RevHalt.RelativeR1.LPO_Eval_eq_LPO_R1_All
#print axioms RevHalt.RelativeR1.LPO_mono_R1
#print axioms RevHalt.RelativeR1.LPO_R1_empty_trivial
#print axioms RevHalt.RelativeR1.DichotomyE_R1_iff_LPO_R1

#print axioms RevHalt.RelativeR1.CutBit.BitCutLink
#print axioms RevHalt.RelativeR1.CutBit.bit_truth_to_cut_witness_pointwise
#print axioms RevHalt.RelativeR1.CutBit.bit_truth_to_cut_selector
#print axioms RevHalt.RelativeR1.CutBit.AdmBit_not_admits_const
