import RevHalt.Dynamics.Core.Fork
import RevHalt.Dynamics.Core.RefSystem
import Mathlib.Data.Rat.Floor

namespace Example

open RevHalt
open RevHalt.Dynamics.Core

/-!
1) “±0 bounds” at the RefSystem (Cut) level.

Intuition: if you can certify `x ≥ ε` then you also get `x ≥ 0`,
and from `x ≥ 0` you get `x ≥ -ε`. So you get a certified “±0 window”
in the *Cut* sense (nested lower bounds).
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
  cut0_to_cut_neg (E := E) (M := M) (x := x) hε (cut_pos_to_cut0 (E := E) (M := M) (x := x) hε h)

end CutBounds

/-!
2) Fork on the “0 pivot” (local bifurcation, no global choice).

Here we take `PropT = Sentence` so the pivot can literally be `E.Cut 0 x`.
Left branch = commit `Cut 0 x` (the “+0 side”),
Right branch = commit `Not (Cut 0 x)` (the “-0 side” in the sense “not ≥ 0”).
-/

namespace ZeroFork

variable {Code Model Sentence Referent : Type}
variable (E : RefSystem Model Sentence Referent)

-- Here PropT = Sentence
variable (ctx : EnrichedContext Code Sentence)
variable (T0 : TheoryNode ctx)
variable (x : Referent)

abbrev p0 : Sentence := E.Cut 0 x

-- certificates (provided by your verifier/oracle layer)
variable (hp0  : ctx.Truth (p0 (E := E) (x := x)))
variable (hnp0 : ctx.Truth (ctx.Not (p0 (E := E) (x := x))))

def F0 : Fork ctx T0 := Fork.ofPivot ctx T0 (p0 (E := E) (x := x))

def T_ge0 : TheoryNode ctx := (F0 (E := E) (ctx := ctx) (T0 := T0) (x := x)).left hp0
def T_lt0 : TheoryNode ctx := (F0 (E := E) (ctx := ctx) (T0 := T0) (x := x)).right hnp0

theorem edge_to_ge0 :
    Edge ctx T0 ((Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).left hp0) :=
  Fork.ofPivot_edge_left ctx T0 (p0 (E := E) (x := x)) hp0

theorem edge_to_lt0 :
    Edge ctx T0 ((Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).right hnp0) :=
  Fork.ofPivot_edge_right ctx T0 (p0 (E := E) (x := x)) hnp0

theorem not_both_sound_0pivot :
  ¬ (TheorySound ctx (Extend T0.theory (p0 (E := E) (x := x))) ∧
     TheorySound ctx (Extend T0.theory (ctx.Not (p0 (E := E) (x := x))))) :=
  (Fork.ofPivot ctx T0 (p0 (E := E) (x := x))).exclusion

end ZeroFork

end Example
