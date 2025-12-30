/-
  RevHalt/Instances/PA/OmegaDyadicLink.lean

  Next step: PA-facing dyadic link for Ω-access.

  What this file does (no sorries):
  - Defines the rational dyadic value `k/2^n` from your `DyadicCode`.
  - Repackages the already-proved Ω-side fact: `CutGe(k/2^n)` is Σ₁ (r.e.).
  - Introduces a clean PA interface: an encoding of dyadic `CutGe` as a PA Σ₁ (Halt) sentence,
    with a single spec lemma as the bridge.

  This is the correct "arithmetical" next move:
  it isolates exactly what the PA/Arithmetization layer must realize.

  **Contrast with Logic/Separation**:
  - `OmegaDyadicLink` handles `CutGe` (Reachability), which is **Σ₁** and accessible.
  - `OmegaSigmaSeparation` handles `WinTruth` (Stabilization), which is **Σ₂** (has a Π₁ component) and inaccessible.
  The "Link" here is strictly for the Σ₁ approximations.
-/

import RevHalt.Dynamics.Instances.OmegaAccessSchemas
import RevHalt.Instances.PA.DyadicArith

import Mathlib.Algebra.Order.Ring.Pow

namespace RevHalt.Instances.PA

open RevHalt.Dynamics.Instances.OmegaChaitin
open RevHalt.Dynamics.Instances.OmegaChaitin.LimitSemantics
open RevHalt.Dynamics.Instances.OmegaChaitin.AccessSchemas

/-! ## 1) Dyadic value as a rational (k/2^n) from a DyadicCode -/

/-- Interpret a dyadic descriptor as the rational (k/2^n). -/
def dyadicVal (d : Dyadic) : ℚ :=
  ((d.k : ℚ) / (2 ^ d.n))

/-- Interpret a dyadic PA code as the rational (k/2^n). -/
def dyadicValCode (c : DyadicCode) : ℚ :=
  dyadicVal (decodeDyadic c)

/-- Ω-truth of a dyadic CutGe. -/
def OmegaCutGeDyad (c : DyadicCode) : Prop :=
  OmegaTruth (OmegaSentence.CutGe (dyadicValCode c))

/-! ## 2) Pure Ω-side fact: dyadic CutGe is Σ₁ (schema object) -/

/-- Dyadic CutGe is Σ₁: `OmegaCutGeDyad c ↔ ∃t, OmegaApprox t ≥ dyadicValCode c`. -/
def OmegaCutGeDyad_is_sigma1 (c : DyadicCode) :
    Sigma1Prop (OmegaCutGeDyad c) :=
  -- reuse the generic schema from OmegaAccessSchemas
  let base := CutGe_is_sigma1 (dyadicValCode c)
  { R := base.R
    decR := base.decR
    spec := by simp only [OmegaCutGeDyad]; exact base.spec }

/-!
  At this point we have the arithmetic classification on the Ω side.

  Next: expose the PA interface that realizes the Σ₁ schema as a concrete PA "Halt" sentence.
-/


/-! ## 3) PA interface: encode dyadic CutGe as a PA Σ₁ sentence (Halt) -/

/-- Minimal interface for "Σ₁ in PA" as a Halt sentence.

You can instantiate this using *your existing* PA encoding of r.e. predicates.
We keep it abstract here to avoid smuggling construction choices into the core statement.
-/
structure DyadicCutPAEncoding where
  /-- External truth predicate for PA-sentences (your PA Truth semantics). -/
  PATruth : PASentence → Prop

  /-- Compile a dyadic code into a PA Halt index (Σ₁ code). -/
  cutHaltCode : DyadicCode → ℕ

  /-- The bridge spec: PA truth of the Halt sentence matches Ω truth of the dyadic CutGe. -/
  cut_spec : ∀ c : DyadicCode,
    PATruth (PASentence.Halt (cutHaltCode c)) ↔ OmegaCutGeDyad c

/-- The PA sentence corresponding to dyadic CutGe under an encoding. -/
def DyadicCutPAEncoding.cutSentence (E : DyadicCutPAEncoding) (c : DyadicCode) : PASentence :=
  PASentence.Halt (E.cutHaltCode c)

/-- Sanity: the PA sentence is syntactically Σ₁ (by construction). -/
theorem DyadicCutPAEncoding.cutSentence_isSigma1 (E : DyadicCutPAEncoding) (c : DyadicCode) :
    IsSigma1Sentence (E.cutSentence c) := by
  refine ⟨E.cutHaltCode c, rfl⟩

/-- Main bridge lemma: the dyadic CutGe truth is exactly the PA truth of its Halt-encoding. -/
theorem DyadicCutPAEncoding.cutSentence_correct (E : DyadicCutPAEncoding) (c : DyadicCode) :
    E.PATruth (E.cutSentence c) ↔ OmegaCutGeDyad c := by
  simpa [DyadicCutPAEncoding.cutSentence] using (E.cut_spec c)

end RevHalt.Instances.PA
