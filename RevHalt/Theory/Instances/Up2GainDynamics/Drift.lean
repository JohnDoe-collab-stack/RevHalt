import RevHalt.Theory.Instances.Up2GainDynamics

namespace RevHalt
namespace Up2GainDynamics

open Set
open RevHalt.Up2Gain

/-!
  ============================
  Drift counterexample (Option B)
  ============================

  Key idea:
  If Γ contains every `Ask n`, then `Root` is internally provable from Γ
  by the O-rule (infinitary branching at Root).

  Therefore, if at the ω-union we have all `Ask n` but still `Root ∉ ωΓ`,
  then `Cn (ωΓ) ≠ ωΓ`, hence `ωΓ` is not OmegaAdmissible.
-/

/-- If Γ contains all `Ask n`, then `Root` is internally provable from Γ. -/
lemma root_mem_Cn_of_allAsk (Γ : Set Pos)
    (hAsk : ∀ n : ℕ, Pos.Ask n ∈ Γ) :
    Pos.Root ∈ Cn Γ := by
  -- membership in Cn is Provable
  show Provable Γ Pos.Root
  intro S hS
  -- all Ask n are in S because they are Γ-axioms
  have hAskS : ∀ n : ℕ, S (Pos.Ask n) := by
    intro n
    exact hS.1 (Pos.Ask n) (hAsk n)

  -- Root has moves
  have hMoves : hasMoves Pos.Root := by
    refine ⟨Pos.Ask 0, ?_⟩
    -- canMove Root (Ask 0) reduces to oCanMove Root (Ask 0)
    simp [canMove, turnFn, oCanMove]

  -- all O-moves from Root land in S (because they are all Ask n)
  have hAll : ∀ q : Pos, oCanMove Pos.Root q → S q := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact hAskS n

  -- apply the O-closure clause at Root
  exact hS.2.2 Pos.Root (by simp [turnFn]) hMoves hAll

/-- “Pure drift” criterion: if Γ has all Ask n but not Root, then Γ is not ω-admissible. -/
theorem not_OmegaAdmissible_of_allAsk_rootNot (Γ : Set Pos)
    (hAsk : ∀ n : ℕ, Pos.Ask n ∈ Γ)
    (hRoot : Pos.Root ∉ Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) Γ := by
  intro hOA
  have hEq : Cn Γ = Γ := hOA.1
  have hRootCn : Pos.Root ∈ Cn Γ := root_mem_Cn_of_allAsk (Γ := Γ) hAsk
  have : Pos.Root ∈ Γ := by simpa [hEq] using hRootCn
  exact hRoot this

/--
Drift specialized to your ω-union `ωΓ Γ0`:

If every Ask n appears somewhere along the orbit (hence in ωΓ),
and Root never appears at any finite stage (hence not in ωΓ),
then ωΓ is not OmegaAdmissible.
-/
theorem drift_not_OmegaAdmissible_ωΓ_of_progressive_asks (Γ0 : Set Pos)
    (hAsk : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (chain Γ0 k).Γ)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) := by
  -- derive: all Ask n are in ωΓ
  have hAskω : ∀ n : ℕ, Pos.Ask n ∈ ωΓ Γ0 := by
    intro n
    rcases hAsk n with ⟨k, hk⟩
    -- ωΓ Γ0 = {p | ∃ k, p ∈ (chain Γ0 k).Γ}
    exact ⟨k, hk⟩

  -- derive: Root is not in ωΓ
  have hRootω : Pos.Root ∉ ωΓ Γ0 := by
    intro h
    rcases h with ⟨k, hk⟩
    exact hRoot k hk

  -- conclude by the pure drift criterion
  exact not_OmegaAdmissible_of_allAsk_rootNot (Γ := ωΓ Γ0) hAskω hRootω

end Up2GainDynamics
end RevHalt
