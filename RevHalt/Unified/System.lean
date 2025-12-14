import RevHalt.Unified.Core
import RevHalt.Unified.Closure
import RevHalt.Unified.MasterClosure
import RevHalt.Unified.RefSystem

import Mathlib.Data.Set.Basic

/-!
RevHalt.Unified.System

Goal: turn your aligned layers (Closure + Rev/T1 + Master/T2/T3) into a single
“exploitable system” API: define a canonical Gap, prove invariances, and provide
witness extractors.

This is a *wrapper layer*: it should not change your math, only package it.
-/

namespace RevHalt_Unified

open Set

universe u v

/-- Canonical “gap” object: verifiable-but-not-provable (empty context). -/
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

/-
  =========================
  Kit-invariance add-on
  =========================

  If you want kit-invariance of the “verifiable” side, phrase it through CloRev.
  This is orthogonal to VerifiableContext (which only mentions Halts/LR),
  but your Closure file already gives invariance in K under DetectsMonotone.

  So define a “kit-gap” and prove it is invariant in K.
-/

/-- Gap defined via kit-verdict closure instead of Halts (robust verifiability). -/
def GapRev {_ PropT : Type}
    (LR : Set PropT → PropT → Trace)
    (K : RHKit) : Set PropT :=
  (CloRev (LR := LR) K (∅ : Set PropT)) \ (∅ : Set PropT) -- placeholder: you usually subtract ProvableSet of some ctx

/-
  In practice you’ll want:
  GapRev ctx K := CloRev K ∅ \ ProvableSet ctx
  but that needs ctx.Provable; keep it in a structure that includes both LR and Provable.
-/

/-- A compact “system” bundle for robust gap reasoning (LR + Provable + kits). -/
structure GapSystem (Code PropT : Type) extends VerifiableContext Code PropT where
  K : RHKit
  hK : DetectsMonotone K

namespace GapSystem

/-- Robust verifiable set (empty context) via the chosen kit. -/
def VerRev {Code PropT : Type} (S : GapSystem Code PropT) : Set PropT :=
  CloRev (LR := S.LR) S.K (∅ : Set PropT)

/-- Robust gap: kit-verifiable but not provable. -/
def GapK {Code PropT : Type} (S : GapSystem Code PropT) : Set PropT :=
  (VerRev S) \ (ProvableSet S.toEnrichedContext)

@[simp] theorem mem_VerRev_iff {Code PropT : Type} (S : GapSystem Code PropT) (p : PropT) :
    p ∈ VerRev S ↔ Rev0_K S.K (S.LR ∅ p) := by
  rfl

/-- VerRev equals CloK extensionally (T1 on traces). -/
theorem VerRev_eq_CloK {Code PropT : Type} (S : GapSystem Code PropT) :
    VerRev S = CloK (LR := S.LR) (∅ : Set PropT) := by
  ext p
  -- membership: Rev0_K ↔ Halts, then unfold CloK/CloRev
  have h : Rev0_K S.K (S.LR ∅ p) ↔ Halts (S.LR ∅ p) := T1_traces S.K S.hK (S.LR ∅ p)
  simpa [VerRev, CloRev, CloK] using h

/-- Robust gap is nonempty (same witness as the CloK gap). -/
theorem gapK_nonempty {Code PropT : Type}
    (S : GapSystem Code PropT) :
    ∃ p, p ∈ GapK S := by
  -- use gap_nonempty on the underlying VerifiableContext + transport via VerRev_eq_CloK
  obtain ⟨p, hp⟩ := gap_nonempty (ctx := S.toVerifiableContext)
  refine ⟨p, ?_⟩
  rcases hp with ⟨hCloK, hNotProv⟩
  have hVerRev : p ∈ VerRev S := by
    -- rewrite VerRev to CloK
    have : VerRev S = CloK (LR := S.LR) (∅ : Set PropT) := VerRev_eq_CloK S
    simpa [this] using hCloK
  exact ⟨hVerRev, hNotProv⟩

/-- Kit-invariance (replace K by any other valid kit): membership in VerRev is invariant. -/
theorem VerRev_invariant {Code PropT : Type}
    (S : GapSystem Code PropT) (K₂ : RHKit) (h₂ : DetectsMonotone K₂) :
    ∀ p, (p ∈ CloRev (LR := S.LR) S.K (∅ : Set PropT)) ↔ (p ∈ CloRev (LR := S.LR) K₂ (∅ : Set PropT)) := by
  intro p
  exact CloRev_mem_invariant (LR := S.LR) S.K K₂ S.hK h₂ (∅ : Set PropT) p

end GapSystem

end RevHalt_Unified
