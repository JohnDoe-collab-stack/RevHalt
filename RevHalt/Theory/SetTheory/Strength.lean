import RevHalt.Theory.SetTheory.ZFC_System
import RevHalt.Theory.SetTheory.Semantics
import RevHalt.Theory.Complementarity
import RevHalt.Theory.Impossibility
import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Theory.SetTheory.Strength

Formal Proof that the RevHalt Complementarity System is Strictly Stronger than ZFC.

We derive strict superiority from standard properties:
1.  **Consistency**: A Standard Model of ZFC exists (Soundness).
2.  **Arithmetization**: The set of disprovable halting sentences is Recursively Enumerable.

Using these, we construct a witness via Diagonalization (`Impossibility.diagonal_bridge`),
which is a true non-halting sentence independent of ZFC (`witness_e`).
We then construct `RevHalt_System` as an extension of ZFC including this negative truth.
-/

namespace RevHalt.SetTheory

open Formula RevHalt
open Nat.Partrec

-- =====================================================================================
-- 1. Standard Model & Soundness
-- =====================================================================================

/--
  Axiom: Existence of a Standard Model of ZFC.
  This implies Con(ZFC) and provides a semantic Truth definition.
-/
axiom ZFC_Model_Exists : ∃ (D : Type) (M : Structure D), IsModel M ZFC_Set ∧ Nonempty D

noncomputable abbrev StandardModel_D : Type := Classical.choose ZFC_Model_Exists
noncomputable abbrev StandardModel_Exists_M : ∃ M : Structure StandardModel_D, IsModel M ZFC_Set ∧ Nonempty StandardModel_D :=
  Classical.choose_spec ZFC_Model_Exists

noncomputable abbrev StandardModel_Structure : Structure StandardModel_D :=
  Classical.choose StandardModel_Exists_M

noncomputable abbrev StandardModel_Props : IsModel StandardModel_Structure ZFC_Set ∧ Nonempty StandardModel_D :=
  Classical.choose_spec StandardModel_Exists_M

noncomputable abbrev StandardModel_IsModel : IsModel StandardModel_Structure ZFC_Set :=
  StandardModel_Props.1

noncomputable instance : Inhabited StandardModel_D :=
  Classical.inhabited_of_nonempty StandardModel_Props.2

/--
  Lemma: ZFC is Sound with respect to Standard Model.
  Derives Γ φ → IsModel M Γ → M ⊨ φ
-/
theorem h_ZFC_Sound : ∀ φ, ZFC_Provable φ → (∀ val : Valuation StandardModel_D, satisfies StandardModel_Structure val φ) := by
  intro φ hProv
  exact Soundness hProv _ StandardModel_IsModel

-- =====================================================================================
-- 2. Arithmetization & Diagonalization
-- =====================================================================================

/--
  Axiom: Correctness of Encoding.
  Standard Model matches Rev0_K on encoded sentences.
  e halts ↔ StandardModel ⊨ encode_halt(e)
-/
axiom h_encode_correct : ∀ e, Rev0_K Authentic_ZFC_System.K (Authentic_ZFC_System.Machine e) ↔ (∀ val : Valuation StandardModel_D, satisfies StandardModel_Structure val (encode_halt_FOL e))

/--
  Axiom: Provability of Negation is R.E.
  There exists a partial recursive function `f` that semi-decides `ZFC ⊢ ¬encode_halt(c)`.
-/
axiom ProvableNot_RE : ∃ f : Code → (Nat →. Nat),
  Partrec₂ f ∧
  ∀ c, ZFC_Provable (RevHalt.SetTheory.not (encode_halt_FOL c)) ↔ (∃ x, x ∈ f c 0)

/--
  Derive the Independent Witness using Diagonal Bridge.
  We target `target(c) := ZFC ⊢ ¬encode_halt(c)`.
  Diagonal bridge gives `e` such that: `Rev0_K e ↔ target(e)`.
-/
noncomputable def Independent_Witness_Spec : ∃ e : Code,
    Rev0_K Authentic_ZFC_System.K (Authentic_ZFC_System.Machine e) ↔
    ZFC_Provable (RevHalt.SetTheory.not (encode_halt_FOL e)) := by
  rcases ProvableNot_RE with ⟨f, hf_rec, hf_prop⟩
  let K := Authentic_ZFC_System.K
  -- Prove hK manually for the Standard Kit
  have hK : DetectsMonotone K := Authentic_ZFC_System.h_canon

  let target := fun c => ZFC_Provable (RevHalt.SetTheory.not (encode_halt_FOL c))
  -- Apply diagonal bridge
  have hDiag := diagonal_bridge K hK f hf_rec target hf_prop
  exact hDiag

noncomputable def witness_e : Code := Classical.choose Independent_Witness_Spec
noncomputable def witness_phi : Formula := RevHalt.SetTheory.not (encode_halt_FOL witness_e)

/--
  The Diagonal Property for witness_e.
  Halts(e) ↔ ZFC ⊢ ¬Halts(e)
-/
lemma h_diag_prop :
  Rev0_K Authentic_ZFC_System.K (Authentic_ZFC_System.Machine witness_e) ↔
  ZFC_Provable witness_phi :=
  Classical.choose_spec Independent_Witness_Spec

-- =====================================================================================
-- 3. Proof of Independence
-- =====================================================================================

/--
  Lemma: witness_e DOES NOT HALT.
  Proof by Contradiction.
-/
lemma witness_not_halting : ¬ Rev0_K Authentic_ZFC_System.K (Authentic_ZFC_System.Machine witness_e) := by
  intro hHalts
  -- 1. Diagonal: Halts -> Provable(¬Halts)
  have hProvNot : ZFC_Provable witness_phi := h_diag_prop.mp hHalts
  -- 2. Soundness: Provable(¬Halts) -> True(¬Halts)
  have hTrueNot : ∀ val : Valuation StandardModel_D, satisfies StandardModel_Structure val witness_phi :=
    h_ZFC_Sound _ hProvNot
  -- 3. Correctness: Halts -> True(Halts)
  have hTrueHalts : ∀ val : Valuation StandardModel_D, satisfies StandardModel_Structure val (encode_halt_FOL witness_e) :=
    (h_encode_correct witness_e).mp hHalts
  -- 4. Contradiction
  let val : Valuation StandardModel_D := fun _ => default
  exact (hTrueNot val) (hTrueHalts val)

/--
  Lemma: ZFC does NOT prove witness_phi (which is ¬Halts).
-/
lemma witness_unprovable : ¬ ZFC_Provable witness_phi := by
  intro hProv
  -- Diagonal: Provable(¬Halts) -> Halts
  have hHalts : Rev0_K Authentic_ZFC_System.K (Authentic_ZFC_System.Machine witness_e) :=
    h_diag_prop.mpr hProv
  exact witness_not_halting hHalts

-- =====================================================================================
-- 4. RevHalt System
-- =====================================================================================

/--
  Monotonicity of Derives.
-/
theorem Derives_monotone {Γ Δ : Set Formula} (h : Γ ⊆ Δ) {φ : Formula} (d : Derives Γ φ) : Derives Δ φ := by
  induction d with
  | hyp hp => exact Derives.hyp (h hp)
  | log hl => exact Derives.log hl
  | mp _ _ ih1 ih2 => exact Derives.mp ih1 ih2
  | gen _ ih => exact Derives.gen ih

/--
  RevHalt System Set (Manual Definition).
  Defined as ZFC + { witness_phi }.
  This represents the "Sound Extension" predicted by Complementarity Theory
  when applied to the "Negative" Halting Problem.
  Since witness_phi is True (in Standard Model), this system is Sound.
-/
def RevHalt_System_Set : Set Formula :=
  ZFC_Set ∪ { witness_phi }

def RevHalt_Provable (φ : Formula) : Prop := Derives RevHalt_System_Set φ

theorem RevHalt_Strictly_Stronger_Than_ZFC :
  ∃ φ, (RevHalt_Provable φ ∧ ¬ ZFC_Provable φ) ∧ (∀ ψ, ZFC_Provable ψ → RevHalt_Provable ψ) := by
  let φ := witness_phi
  -- 1. Provable in RevHalt
  have hIn : φ ∈ RevHalt_System_Set := Set.mem_union_right _ (Set.mem_singleton _)
  have hProv : RevHalt_Provable φ := Derives.hyp hIn
  -- 2. Unprovable in ZFC
  let hUnprov := witness_unprovable
  -- 3. Inclusion
  have hIncl : ∀ ψ, ZFC_Provable ψ → RevHalt_Provable ψ := by
    intro ψ hZFC
    apply Derives_monotone Set.subset_union_left hZFC

  -- 4. Result
  refine Exists.intro φ ?_
  exact ⟨⟨hProv, hUnprov⟩, hIncl⟩

end RevHalt.SetTheory
