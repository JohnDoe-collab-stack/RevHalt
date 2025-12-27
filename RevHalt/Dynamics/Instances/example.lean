import RevHalt.Dynamics.Core.Fork
import RevHalt.Dynamics.Core.RefSystem
import RevHalt.Dynamics.Instances.OmegaChaitin
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Example

open RevHalt
open RevHalt.Dynamics.Core

/-!
1) “±0 bounds” at the RefSystem (Cut) level.

If `Cut q x` is interpreted as “x ≥ q”, then:
- from `x ≥ ε` (with 0 ≤ ε) we get `x ≥ 0`
- from `x ≥ 0` we get `x ≥ -ε`
So we get a certified “±0 window” in the Cut sense (nested lower bounds).
-/

namespace CutBounds

variable {Model Sentence Referent : Type}
variable (E : RefSystem Model Sentence Referent)
variable {M : Model} {x : Referent} {ε : ℚ}

lemma cut_pos_to_cut0 (hε : (0 : ℚ) ≤ ε)
    (h : E.Sat M (E.Cut ε x)) :
    E.Sat M (E.Cut 0 x) :=
  E.cut_antimono (M := M) (q := 0) (q' := ε) (x := x) hε h

lemma cut0_to_cut_neg (hε : (0 : ℚ) ≤ ε)
    (h : E.Sat M (E.Cut 0 x)) :
    E.Sat M (E.Cut (-ε) x) := by
  have hle : (-ε) ≤ (0 : ℚ) := by
    exact neg_nonpos.mpr hε
  exact E.cut_antimono (M := M) (q := -ε) (q' := 0) (x := x) hle h

lemma cut_pos_to_cut_neg (hε : (0 : ℚ) ≤ ε)
    (h : E.Sat M (E.Cut ε x)) :
    E.Sat M (E.Cut (-ε) x) :=
  cut0_to_cut_neg (E := E) (M := M) (x := x) (ε := ε) hε
    (cut_pos_to_cut0 (E := E) (M := M) (x := x) (ε := ε) hε h)

/-!
**Dyadic specialization** (this is the “pm_zero_dyadic” you asked to eliminate `sorry` for):
take ε = 1 / 2^n and get `Cut ε -> Cut 0 -> Cut (-ε)`.
-/

def dyad (n : ℕ) : ℚ := (1 : ℚ) / ((2 : ℚ) ^ n)

lemma dyad_nonneg (n : ℕ) : (0 : ℚ) ≤ dyad n := by
  unfold dyad
  positivity

theorem pm_zero_dyadic (n : ℕ)
    (h : E.Sat M (E.Cut (dyad n) x)) :
    E.Sat M (E.Cut 0 x) ∧ E.Sat M (E.Cut (-(dyad n)) x) := by
  have hε : (0 : ℚ) ≤ dyad n := dyad_nonneg (n := n)
  have h0 : E.Sat M (E.Cut 0 x) :=
    cut_pos_to_cut0 (E := E) (M := M) (x := x) (ε := dyad n) hε h
  have hneg : E.Sat M (E.Cut (-(dyad n)) x) :=
    cut0_to_cut_neg (E := E) (M := M) (x := x) (ε := dyad n) hε h0
  exact ⟨h0, hneg⟩

end CutBounds

/-!
2) Fork on the “0 pivot” (local bifurcation, no global choice).

We take `PropT = Sentence`, so the pivot can literally be `E.Cut 0 x`.
Left branch commits `Cut 0 x` (the “≥ 0 side”),
Right branch commits `Not (Cut 0 x)` (the “< 0 side” as “not ≥ 0”).
-/

namespace ZeroFork

variable {Code Model Sentence Referent : Type}
variable (E : RefSystem Model Sentence Referent)

-- PropT = Sentence
variable (ctx : EnrichedContext Code Sentence)
variable (T0 : TheoryNode ctx)
variable (x : Referent)

def p0 : Sentence := E.Cut 0 x

-- certificates (provided by your verifier/oracle layer)
variable (hp0  : ctx.Truth (p0 (E := E) (x := x)))
variable (hnp0 : ctx.Truth (ctx.Not (p0 (E := E) (x := x))))

def F0 : Fork ctx T0 :=
  Fork.ofPivot ctx T0 (p0 (E := E) (x := x))

def T_ge0 : TheoryNode ctx :=
  (F0 (E := E) (ctx := ctx) (T0 := T0) (x := x)).left hp0

def T_not_ge0 : TheoryNode ctx :=
  (F0 (E := E) (ctx := ctx) (T0 := T0) (x := x)).right hnp0

theorem edge_to_ge0 :
    Edge ctx T0 ((Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).left hp0) :=
  Fork.ofPivot_edge_left ctx T0 (p0 (E := E) (x := x)) hp0

theorem edge_to_not_ge0 :
    Edge ctx T0 ((Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).right hnp0) :=
  Fork.ofPivot_edge_right ctx T0 (p0 (E := E) (x := x)) hnp0

theorem not_both_sound_0pivot :
  ¬ (TheorySound ctx (Extend T0.theory (p0 (E := E) (x := x))) ∧
     TheorySound ctx (Extend T0.theory (ctx.Not (p0 (E := E) (x := x))))) :=
  (Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).exclusion

end ZeroFork

/-!
3) Dyadic-cut **kit invariance** in the Ω instance (your “OmegaLike invariance for dyadic cuts”).

This is the clean “plumbing” statement:
for any valid kits K₁ K₂, the Rev verdict for a dyadic cut query is identical.
-/

namespace OmegaDyadic

open RevHalt.Dynamics.Instances.OmegaChaitin
open RevHalt.Dynamics.Instances.OmegaChaitin.CutComputable

theorem omega_dyadic_cut_kit_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂)
    (n : ℕ) :
    Rev0_K K₁ (LR_omega ∅ (OmegaSentence.CutGe ((1 : ℚ) / (2 ^ n)))) ↔
    Rev0_K K₂ (LR_omega ∅ (OmegaSentence.CutGe ((1 : ℚ) / (2 ^ n)))) := by
  exact omega_cut_kit_invariant (K₁ := K₁) (K₂ := K₂) (h₁ := h₁) (h₂ := h₂)
    (q := (1 : ℚ) / (2 ^ n))

theorem omega_pm0_dyadic_cut_kit_invariant
    (K₁ K₂ : RHKit) (h₁ : DetectsMonotone K₁) (h₂ : DetectsMonotone K₂)
    (n : ℕ) :
    (Rev0_K K₁ (LR_omega ∅ (OmegaSentence.CutGe 0)) ↔
     Rev0_K K₂ (LR_omega ∅ (OmegaSentence.CutGe 0))) ∧
    (Rev0_K K₁ (LR_omega ∅ (OmegaSentence.CutGe ((1 : ℚ) / (2 ^ n)))) ↔
     Rev0_K K₂ (LR_omega ∅ (OmegaSentence.CutGe ((1 : ℚ) / (2 ^ n))))) ∧
    (Rev0_K K₁ (LR_omega ∅ (OmegaSentence.CutGe (-( (1 : ℚ) / (2 ^ n))))) ↔
     Rev0_K K₂ (LR_omega ∅ (OmegaSentence.CutGe (-( (1 : ℚ) / (2 ^ n)))))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact omega_cut_kit_invariant (K₁ := K₁) (K₂ := K₂) (h₁ := h₁) (h₂ := h₂) (q := 0)
  · exact omega_dyadic_cut_kit_invariant (K₁ := K₁) (K₂ := K₂) (h₁ := h₁) (h₂ := h₂) (n := n)
  · exact omega_cut_kit_invariant (K₁ := K₁) (K₂ := K₂) (h₁ := h₁) (h₂ := h₂)
      (q := -((1 : ℚ) / (2 ^ n)))

end OmegaDyadic

end Example
