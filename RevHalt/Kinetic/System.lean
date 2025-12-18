import RevHalt.Kinetic.MasterClosure

/-!
# RevHalt.Kinetic.System

Gap API: defines Gap, GapTruth, GapSystem.

## Contents
- `Gap`: verifiable-but-not-provable (empty context)
- `GapTruth`: true-but-not-provable
- `GapSystem`: compact bundle for robust gap reasoning
-/

namespace RevHalt

open Set

/-- Canonical "gap" object: verifiable-but-not-provable (empty context). -/
def Gap {Code PropT : Type} (ctx : VerifiableContext Code PropT) : Set PropT :=
  (CloK (LR := ctx.LR) (∅ : Set PropT)) \ (ProvableSet ctx.toEnrichedContext)

/-- Alternative gap presentation: True-but-not-provable. -/
def GapTruth {Code PropT : Type} (ctx : VerifiableContext Code PropT) : Set PropT :=
  { p | ctx.Truth p ∧ ¬ ctx.Provable p }

@[simp] theorem mem_Gap_iff {Code PropT : Type} (ctx : VerifiableContext Code PropT) (p : PropT) :
    p ∈ Gap ctx ↔ (p ∈ CloK (LR := ctx.LR) (∅ : Set PropT)) ∧ p ∉ ProvableSet ctx.toEnrichedContext :=
  by rfl

@[simp] theorem mem_GapTruth_iff {Code PropT : Type} (ctx : VerifiableContext Code PropT) (p : PropT) :
    p ∈ GapTruth ctx ↔ (ctx.Truth p ∧ ¬ ctx.Provable p) :=
  by rfl

/-- The bridge makes `Gap` and `GapTruth` extensionally the same set. -/
theorem Gap_eq_GapTruth {Code PropT : Type} (ctx : VerifiableContext Code PropT) :
    Gap ctx = GapTruth ctx := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hCloK, hNotProv⟩
    -- CloK-membership ↔ Halts ↔ Truth (bridge)
    have hHalts : Halts (ctx.LR ∅ p) := (mem_CloK_iff (LR := ctx.LR) (Γ := (∅ : Set PropT)) (φ := p)).1 hCloK
    have hTrue : ctx.Truth p := (ctx.h_bridge p).2 hHalts
    exact ⟨hTrue, hNotProv⟩
  · intro hp
    rcases hp with ⟨hTrue, hNotProv⟩
    have hHalts : Halts (ctx.LR ∅ p) := (ctx.h_bridge p).1 hTrue
    have hCloK : p ∈ CloK (LR := ctx.LR) (∅ : Set PropT) :=
      (mem_CloK_iff (LR := ctx.LR) (Γ := (∅ : Set PropT)) (φ := p)).2 hHalts
    exact ⟨hCloK, hNotProv⟩

/-- Minimal exploit: gap is nonempty (produces a witness). -/
theorem gap_nonempty {Code PropT : Type}
    (ctx : VerifiableContext Code PropT) :
    ∃ p, p ∈ Gap ctx := by
  -- from T2 in your EnrichedContext layer
  obtain ⟨p, hTrue, hNotProv⟩ := true_but_unprovable_exists ctx.toEnrichedContext
  -- Truth -> CloK via bridge
  have hHalts : Halts (ctx.LR ∅ p) := (ctx.h_bridge p).1 hTrue
  have hCloK : p ∈ CloK (LR := ctx.LR) (∅ : Set PropT) :=
    (mem_CloK_iff (LR := ctx.LR) (Γ := (∅ : Set PropT)) (φ := p)).2 hHalts
  refine ⟨p, ?_⟩
  exact ⟨hCloK, hNotProv⟩

/-- Stronger exploit (needs soundness): an independent halting-code exists. -/
theorem independent_witness {Code PropT : Type}
    (ctx : VerifiableContext Code PropT)
    (h_sound : ∀ p, ctx.Provable p → ctx.Truth p) :
    ∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e)) :=
  independent_code_exists ctx.toEnrichedContext h_sound

/-- Gap witness in "Truth" form: extract a true but unprovable proposition. -/
theorem gap_witness_truth {Code PropT : Type} (ctx : VerifiableContext Code PropT) :
    ∃ p, ctx.Truth p ∧ ¬ctx.Provable p :=
  true_but_unprovable_exists ctx.toEnrichedContext

/-- Gap witness in "Halts" form: extract a halting-but-unprovable proposition. -/
theorem gap_witness_halts {Code PropT : Type} (ctx : VerifiableContext Code PropT) :
    ∃ p, Halts (ctx.LR ∅ p) ∧ ¬ctx.Provable p := by
  obtain ⟨p, hT, hNP⟩ := true_but_unprovable_exists ctx.toEnrichedContext
  refine ⟨p, (ctx.h_bridge p).1 hT, hNP⟩

/-
  =========================
  Kit-invariance add-on
  =========================

  For kit-invariant gap reasoning, use `GapSystem` which bundles
  VerifiableContext + a validated RHKit.
-/

/-- A compact "system" bundle for robust gap reasoning (LR + Provable + kits). -/
structure GapSystem (Code PropT : Type) where
  ctx : VerifiableContext Code PropT
  K : RHKit
  hK : DetectsMonotone K

namespace GapSystem

/-- Robust verifiable set (empty context) via the chosen kit. -/
def VerRev {Code PropT : Type} (S : GapSystem Code PropT) : Set PropT :=
  CloRev (LR := S.ctx.LR) S.K (∅ : Set PropT)

/-- Robust gap: kit-verifiable but not provable. -/
def GapK {Code PropT : Type} (S : GapSystem Code PropT) : Set PropT :=
  (VerRev S) \ (ProvableSet S.ctx.toEnrichedContext)

@[simp] theorem mem_VerRev_iff {Code PropT : Type} (S : GapSystem Code PropT) (p : PropT) :
    p ∈ VerRev S ↔ Rev0_K S.K (S.ctx.LR ∅ p) := by
  rfl

/-- VerRev equals CloK extensionally (T1 on traces). -/
theorem VerRev_eq_CloK {Code PropT : Type} (S : GapSystem Code PropT) :
    VerRev S = CloK (LR := S.ctx.LR) (∅ : Set PropT) := by
  ext p
  -- membership: Rev0_K ↔ Halts, then unfold CloK/CloRev
  have h : Rev0_K S.K (S.ctx.LR ∅ p) ↔ Halts (S.ctx.LR ∅ p) := T1_traces S.K S.hK (S.ctx.LR ∅ p)
  simpa [VerRev, CloRev, CloK] using h

/-- Robust gap is nonempty (same witness as the CloK gap). -/
theorem gapK_nonempty {Code PropT : Type}
    (S : GapSystem Code PropT) :
    ∃ p, p ∈ GapK S := by
  -- use gap_nonempty on the underlying VerifiableContext + transport via VerRev_eq_CloK
  obtain ⟨p, hp⟩ := gap_nonempty (ctx := S.ctx)
  refine ⟨p, ?_⟩
  rcases hp with ⟨hCloK, hNotProv⟩
  have hVerRev : p ∈ VerRev S := by
    -- rewrite VerRev to CloK
    have : VerRev S = CloK (LR := S.ctx.LR) (∅ : Set PropT) := VerRev_eq_CloK S
    simpa [this] using hCloK
  exact ⟨hVerRev, hNotProv⟩

/-- Kit-invariance (replace K by any other valid kit): membership in VerRev is invariant. -/
theorem VerRev_invariant {Code PropT : Type}
    (S : GapSystem Code PropT) (K₂ : RHKit) (h₂ : DetectsMonotone K₂) :
    ∀ p, (p ∈ CloRev (LR := S.ctx.LR) S.K (∅ : Set PropT)) ↔ (p ∈ CloRev (LR := S.ctx.LR) K₂ (∅ : Set PropT)) := by
  intro p
  exact CloRev_mem_invariant (LR := S.ctx.LR) S.K K₂ S.hK h₂ (∅ : Set PropT) p

/-- GapK itself is kit-invariant: the verifiable-but-unprovable gap doesn't depend on kit choice. -/
theorem GapK_invariant {Code PropT : Type}
    (S : GapSystem Code PropT) (K₂ : RHKit) (h₂ : DetectsMonotone K₂) :
    ∀ p, (p ∈ GapK S) ↔
         (p ∈ ((CloRev (LR := S.ctx.LR) K₂ (∅ : Set PropT)) \ ProvableSet S.ctx.toEnrichedContext)) := by
  intro p
  constructor
  · intro hp
    rcases hp with ⟨hV, hNP⟩
    have hV' : p ∈ CloRev (LR := S.ctx.LR) K₂ (∅ : Set PropT) :=
      (S.VerRev_invariant K₂ h₂ p).1 (by simpa [VerRev] using hV)
    exact ⟨hV', hNP⟩
  · intro hp
    rcases hp with ⟨hV, hNP⟩
    have hV' : p ∈ CloRev (LR := S.ctx.LR) S.K (∅ : Set PropT) :=
      (S.VerRev_invariant K₂ h₂ p).2 hV
    exact ⟨by simpa [VerRev] using hV', hNP⟩

end GapSystem

end RevHalt
