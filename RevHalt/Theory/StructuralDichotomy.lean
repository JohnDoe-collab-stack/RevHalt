import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Monotone.Basic

namespace RevHalt

/--
Une dichotomie "structurelle" : un opérateur O avec ⊥, un prédicat Sig ("signal"),
invariance du signal, et identification du noyau à ¬Sig.
-/
structure StructuralDichotomy (X : Type) [Preorder X] [Bot X] where
  O : X → X
  mono : Monotone O
  idem : ∀ x, O (O x) = O x
  Sig : X → Prop
  sig_invar : ∀ x, Sig (O x) ↔ Sig x
  ker_iff : ∀ x, O x = ⊥ ↔ ¬ Sig x

namespace StructuralDichotomy

variable {X : Type} [Preorder X] [Bot X] (D : StructuralDichotomy X)

-- Constructif : Sig x → O x ≠ ⊥
theorem sig_imp_ne_bot (x : X) : D.Sig x → D.O x ≠ ⊥ := by
  intro hs hO
  have hns : ¬ D.Sig x := (D.ker_iff x).1 hO
  exact hns hs

-- Constructif : O x ≠ ⊥ → ¬¬Sig x
theorem ne_bot_imp_notnot_sig (x : X) : D.O x ≠ ⊥ → ¬¬ D.Sig x := by
  intro hne hns
  have : D.O x = ⊥ := (D.ker_iff x).2 hns
  exact hne this

-- Ici seulement : classique (¬¬P → P)
theorem ne_bot_imp_sig (x : X) : D.O x ≠ ⊥ → D.Sig x := by
  classical
  intro hne
  have : ¬¬ D.Sig x := D.ne_bot_imp_notnot_sig x hne
  exact Classical.not_not.mp this

theorem sig_iff_ne_bot (x : X) : D.Sig x ↔ D.O x ≠ ⊥ :=
  ⟨D.sig_imp_ne_bot x, D.ne_bot_imp_sig x⟩

end StructuralDichotomy
end RevHalt
