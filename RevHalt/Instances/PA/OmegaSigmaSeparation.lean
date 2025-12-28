/-
  RevHalt.Instances.PA.OmegaSigmaSeparation

  Formalizes the "arithmetical barrier" for Omega access:
  WinTruth (the correct bit of Omega) is NOT uniformly Σ₁ in PA.

  If WinTruth were uniformly Σ₁, we could use PA-Halting to compute Omega,
  which is impossible (OmegaNonComputable).
-/
import RevHalt.Instances.PA.OmegaDyadicLink
import RevHalt.Dynamics.Instances.OmegaTruth
import RevHalt.Dynamics.Instances.OmegaAccessSchemas

import Mathlib.Tactic.FinCases
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding

namespace RevHalt.Instances.PA

-- haltsWithinDec is in OmegaChaitin base
open RevHalt.Dynamics.Instances.OmegaChaitin (haltsWithinDec)
-- WinTruth is in LimitSemantics
open RevHalt.Dynamics.Instances.OmegaChaitin.LimitSemantics (WinTruth)
-- Sigma2Prop and WinTruth_is_sigma2
open RevHalt.Dynamics.Instances.OmegaChaitin.AccessSchemas

/-! ## 1) Uniform Σ₁ notion (project-native) -/

/-- A family `P : α → Prop` is "uniformly Σ₁ via Halt" if there exists a *computable* compilation
    `code : α → ℕ` such that `PATruth (Halt (code a)) ↔ P a` for all `a`. -/
structure UniformlySigma1 {α : Type*} [Primcodable α] (PATruth : PASentence → Prop) (P : α → Prop) where
  code : α → ℕ
  code_computable : Computable code
  spec : ∀ a : α, PATruth (PASentence.Halt (code a)) ↔ P a

/-- Shorthand: WinTruth at depth n, bit a. -/
def WinTruthFamily (input : ℕ × Fin 2) : Prop :=
  WinTruth input.1 input.2

/-! ## 2) Enumerable bits structure (extracted from a uniform Σ₁ compilation) -/

structure OmegaBitEnumerable (PATruth : PASentence → Prop) where
  haltIfBit0 : ℕ → ℕ
  haltIfBit1 : ℕ → ℕ
  h0_computable : Computable haltIfBit0
  h1_computable : Computable haltIfBit1
  spec0 : ∀ n, PATruth (PASentence.Halt (haltIfBit0 n)) ↔ WinTruth n 0
  spec1 : ∀ n, PATruth (PASentence.Halt (haltIfBit1 n)) ↔ WinTruth n 1

/-- From UniformlySigma1 on WinTruthFamily, build OmegaBitEnumerable. -/
def OmegaBitEnumerable.fromUniformSigma1
    {PATruth : PASentence → Prop}
    (U : UniformlySigma1 PATruth WinTruthFamily) :
    OmegaBitEnumerable PATruth where
  haltIfBit0 := fun n => U.code (n, 0)
  haltIfBit1 := fun n => U.code (n, 1)
  h0_computable := by
    -- n ↦ (n,0) is computable, then compose with U.code
    have hpair : Computable (fun n : ℕ => (n, (0 : Fin 2))) := by
      simpa using
        (Computable.pair
          (Computable.id : Computable (fun n : ℕ => n))
          (Computable.const (0 : Fin 2)))
    exact U.code_computable.comp hpair
  h1_computable := by
    -- n ↦ (n,1) is computable, then compose with U.code
    have hpair : Computable (fun n : ℕ => (n, (1 : Fin 2))) := by
      simpa using
        (Computable.pair
          (Computable.id : Computable (fun n : ℕ => n))
          (Computable.const (1 : Fin 2)))
    exact U.code_computable.comp hpair
  spec0 := fun n => U.spec (n, 0)
  spec1 := fun n => U.spec (n, 1)

/-! ## 3) Project-native noncomputability hypothesis -/

open RevHalt.Dynamics.Instances.OmegaChaitin (bitOfNat)

/-- Omega is computable if there is a total computable function returning the correct WinTruth bit. -/
def OmegaComputable : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧
    ∀ n : ℕ, WinTruth n (RevHalt.Dynamics.Instances.OmegaChaitin.bitOfNat (f n))

/-- Hypothesis: Ω is genuinely non-computable (Chaitin). -/
def OmegaNonComputable : Prop := ¬ OmegaComputable

/-- Hypothesis: PA Halting is sound and complete for atomic Halt statements, linked to haltsWithinDec. -/
structure HaltingSoundness (PATruth : PASentence → Prop) where
  soundness : ∀ n, PATruth (PASentence.Halt n) ↔ ∃ t, haltsWithinDec t n 0 = true

/-! ## 4) The separation theorem -/

/-
  We need computability of the bounded evaluator that underlies haltsWithinDec.
  In Mathlib PartrecCode:
  - `Nat.Partrec.Code.evaln_prim` (aka `evaln` is primitive recursive)
  - `Primrec.option_isSome` (projection to Bool)
  give computability of the predicate "halts within t steps".
-/

/-- (Uncurried) computability of haltsWithinDec on triples. -/
private theorem haltsWithinDec_triple_computable :
    Computable (fun x : ℕ × (ℕ × ℕ) => haltsWithinDec x.1 x.2.1 x.2.2) := by
  classical
  -- `haltsWithinDec` is defined in the project as `isSome (evaln ...)`.
  -- `Nat.Partrec.Code.evaln_prim` supplies primrec for the bounded evaluator; `option_isSome` preserves primrec.
  -- The following simp expects the project definition:
  --   haltsWithinDec t p n = ((Nat.Partrec.Code.ofNatCode p).evaln t n).isSome
  -- If your definition is syntactically different, adjust this simp lemma accordingly.
  -- We need to map inputs from ℕ codes to Code objects.
  -- Map: (t, (p, n)) -> ((t, ofNatCode p), n)
  let map_input (x : ℕ × (ℕ × ℕ)) : (ℕ × Nat.Partrec.Code) × ℕ :=
    ((x.1, Nat.Partrec.Code.ofNatCode x.2.1), x.2.2)

  -- Prove map_input is computable (actually Primrec).
  -- We assume Nat.Partrec.Code.ofNatCode corresponds to the standard Denumerable.ofNat.
  have map_prim : Primrec map_input := by
    apply Primrec.pair
    · apply Primrec.pair
      · exact Primrec.fst
      · apply Primrec.comp (Primrec.ofNat (α := Nat.Partrec.Code)) (Primrec.fst.comp Primrec.snd)
    · exact Primrec.snd.comp Primrec.snd

  -- Compose and convert to Computable.
  have h_comp : Computable (fun x => (Nat.Partrec.Code.evaln (map_input x).1.1 (map_input x).1.2 (map_input x).2).isSome) :=
    ((Primrec.option_isSome.comp Nat.Partrec.Code.evaln_prim).comp map_prim).to_comp

  simpa [haltsWithinDec, map_input] using h_comp

/-- Main theorem: under soundness + unique-bit semantics + Ω noncomputable,
    WinTruth cannot be uniformly Σ₁ via Halt. -/
theorem WinTruth_not_uniformly_sigma1
    {PATruth : PASentence → Prop}
    (hNonComp : OmegaNonComputable)
    (hSound : HaltingSoundness PATruth)
    (hUnique : ∀ n, ∃! a, WinTruth n a)
    (hUnif : UniformlySigma1 PATruth (α := ℕ × Fin 2) WinTruthFamily) :
    False := by
  classical
  let enum := OmegaBitEnumerable.fromUniformSigma1 hUnif

  -- For each n, the unique true bit gives a real bounded halting witness on the corresponding Halt-code.
  have exists_halt :
      ∀ n, ∃ t,
        haltsWithinDec t (enum.haltIfBit0 n) 0 = true ∨
        haltsWithinDec t (enum.haltIfBit1 n) 0 = true := by
    intro n
    rcases hUnique n with ⟨a, ha, _⟩
    fin_cases a
    · -- a = 0
      have hP : PATruth (PASentence.Halt (enum.haltIfBit0 n)) :=
        (enum.spec0 n).2 (by simpa using ha)
      rcases (hSound.soundness (enum.haltIfBit0 n)).1 hP with ⟨t, ht⟩
      exact ⟨t, Or.inl ht⟩
    · -- a = 1
      have hP : PATruth (PASentence.Halt (enum.haltIfBit1 n)) :=
        (enum.spec1 n).2 (by simpa using ha)
      rcases (hSound.soundness (enum.haltIfBit1 n)).1 hP with ⟨t, ht⟩
      exact ⟨t, Or.inr ht⟩

  /- Define a computable search step:
     at (n,t) return some 0 if c0 halts by time t,
     else some 1 if c1 halts by time t,
     else none. -/
  let stepPair : ℕ × ℕ → Option ℕ := fun nt =>
    if haltsWithinDec nt.2 (enum.haltIfBit0 nt.1) 0 then some 0
    else if haltsWithinDec nt.2 (enum.haltIfBit1 nt.1) 0 then some 1
    else none

  -- `stepPair` is computable, since haltsWithinDec is computable and we only use conditionals and constants.
  have stepPair_computable : Computable stepPair := by
    -- Build `halts0(nt)` and `halts1(nt)` as computable Bool functions by composing the triple-computable haltsWithinDec.
    have hHWD :
        Computable (fun x : ℕ × (ℕ × ℕ) => haltsWithinDec x.1 x.2.1 x.2.2) :=
      haltsWithinDec_triple_computable

    have c0_comp : Computable enum.haltIfBit0 := enum.h0_computable
    have c1_comp : Computable enum.haltIfBit1 := enum.h1_computable

    have triple0 : Computable (fun nt : ℕ × ℕ => (nt.2, (enum.haltIfBit0 nt.1, 0))) := by
      have h_n : Computable (fun nt : ℕ × ℕ => nt.1) := Computable.fst
      have h_t : Computable (fun nt : ℕ × ℕ => nt.2) := Computable.snd
      have h_c0 : Computable (fun nt : ℕ × ℕ => enum.haltIfBit0 nt.1) := c0_comp.comp h_n
      have h_in : Computable (fun _ : ℕ × ℕ => (0 : ℕ)) := Computable.const 0
      have h_pair : Computable (fun nt : ℕ × ℕ => (enum.haltIfBit0 nt.1, (0 : ℕ))) :=
        (Computable.pair h_c0 h_in)
      exact (Computable.pair h_t h_pair)

    have triple1 : Computable (fun nt : ℕ × ℕ => (nt.2, (enum.haltIfBit1 nt.1, 0))) := by
      have h_n : Computable (fun nt : ℕ × ℕ => nt.1) := Computable.fst
      have h_t : Computable (fun nt : ℕ × ℕ => nt.2) := Computable.snd
      have h_c1 : Computable (fun nt : ℕ × ℕ => enum.haltIfBit1 nt.1) := c1_comp.comp h_n
      have h_in : Computable (fun _ : ℕ × ℕ => (0 : ℕ)) := Computable.const 0
      have h_pair : Computable (fun nt : ℕ × ℕ => (enum.haltIfBit1 nt.1, (0 : ℕ))) :=
        (Computable.pair h_c1 h_in)
      exact (Computable.pair h_t h_pair)

    have halts0_comp : Computable (fun nt : ℕ × ℕ => haltsWithinDec nt.2 (enum.haltIfBit0 nt.1) 0) :=
      hHWD.comp triple0
    have halts1_comp : Computable (fun nt : ℕ × ℕ => haltsWithinDec nt.2 (enum.haltIfBit1 nt.1) 0) :=
      hHWD.comp triple1

    -- Now assemble stepPair using nested conditionals.
    -- stepPair nt = if halts0 nt then some 0 else if halts1 nt then some 1 else none
    have some0 : Computable (fun _ : ℕ × ℕ => (some 0 : Option ℕ)) := Computable.const (some 0)
    have some1 : Computable (fun _ : ℕ × ℕ => (some 1 : Option ℕ)) := Computable.const (some 1)
    have noneO : Computable (fun _ : ℕ × ℕ => (none : Option ℕ)) := Computable.const none
    have inner : Computable (fun nt : ℕ × ℕ =>
        if haltsWithinDec nt.2 (enum.haltIfBit1 nt.1) 0 then (some 1 : Option ℕ) else none) :=
      (Computable.cond halts1_comp some1 noneO)
    exact (Computable.cond halts0_comp some0 inner)

  -- Define the partial search: rfindOpt returns the first `some b` it encounters.
  let searchBit : ℕ →. ℕ := fun n =>
    Nat.rfindOpt (fun t => stepPair (n, t))

  -- `searchBit` is partial recursive (hence we can extract a total Computable function via of_eq_tot).
  have searchBit_partrec : Partrec searchBit := by
    -- `Partrec.rfindOpt` expects a computable₂ function; get it from the computable-on-pairs stepPair.
    have step₂ : Computable₂ (fun n t => stepPair (n, t)) := stepPair_computable.to₂
    -- Partrec in n: Nat.rfindOpt over t
    simpa [searchBit] using (Partrec.rfindOpt step₂)

  -- Show that searchBit is total (Dom) using `exists_halt`.
  have searchBit_dom : ∀ n, (searchBit n).Dom := by
    intro n
    rcases exists_halt n with ⟨t, ht⟩
    -- Use Nat.rfindOpt_dom: Dom ↔ ∃t b, b ∈ stepPair(n,t)
    refine (Nat.rfindOpt_dom).2 ?_
    cases ht with
    | inl h0 =>
      refine ⟨t, 0, ?_⟩
      -- stepPair (n,t) = some 0
      simp [searchBit, stepPair, h0]
    | inr h1 =>
      refine ⟨t, 1, ?_⟩
      -- if c0 doesn't halt, the step can still be some 1; we only need existence of some value.
      -- Here we can witness with 1 directly by showing the second branch triggers.
      -- We don't know c0 at t, so split on it.
      cases h0' : haltsWithinDec t (enum.haltIfBit0 n) 0 <;> simp [searchBit, stepPair, h0', h1]

  -- Define the total decision function as the extracted value from the partial search.
  let decide : ℕ → ℕ := fun n => (searchBit n).get (searchBit_dom n)

  -- `decide` is computable because it is a totalization of a Partrec function.
  have decide_computable : Computable decide := by
    -- For totalization we need membership `decide n ∈ searchBit n`.
    have mem : ∀ n, decide n ∈ searchBit n := by
      intro n
      -- `Part.get_mem` puts the `get` value back into the Part.
      simpa [decide] using (Part.get_mem (searchBit_dom n))
    exact Partrec.of_eq_tot searchBit_partrec mem

  -- Now we contradict OmegaNonComputable by producing a computable correct-bit function.
  apply hNonComp
  refine ⟨decide, decide_computable, ?_⟩
  intro n

  -- Get a concrete witness time `t` for the returned bit.
  have hmem : decide n ∈ searchBit n := by
    simpa [decide] using (Part.get_mem (searchBit_dom n))
  rcases Nat.rfindOpt_spec (by simpa [searchBit] using hmem) with ⟨t, ht⟩
  -- ht : decide n ∈ stepPair (n,t)

  -- Analyze stepPair (n,t) to determine which Halt-code actually halts, then conclude WinTruth via soundness+spec.
  cases h0 : haltsWithinDec t (enum.haltIfBit0 n) 0 <;> simp [stepPair, h0] at ht
  · -- h0 = true, so decide n = 0 and c0 halts
    have hReal : ∃ t, haltsWithinDec t (enum.haltIfBit0 n) 0 = true := ⟨t, by simpa using h0⟩
    have hP : PATruth (PASentence.Halt (enum.haltIfBit0 n)) :=
      (hSound.soundness (enum.haltIfBit0 n)).2 hReal
    have hWin : WinTruth n 0 := (enum.spec0 n).1 hP
    -- decide n = 0, so bitOfNat (decide n) = 0
    -- ht came from simp: decide n = 0
    subst ht
    simpa [RevHalt.Dynamics.Instances.OmegaChaitin.bitOfNat] using hWin
  · -- h0 = false, so stepPair checks c1; ht forces c1 halts and decide n = 1
    cases h1 : haltsWithinDec t (enum.haltIfBit1 n) 0 <;> simp [stepPair, h0, h1] at ht
    have hReal : ∃ t, haltsWithinDec t (enum.haltIfBit1 n) 0 = true := ⟨t, by simpa using h1⟩
    have hP : PATruth (PASentence.Halt (enum.haltIfBit1 n)) :=
      (hSound.soundness (enum.haltIfBit1 n)).2 hReal
    have hWin : WinTruth n 1 := (enum.spec1 n).1 hP
    subst ht
    simpa [RevHalt.Dynamics.Instances.OmegaChaitin.bitOfNat] using hWin

/-! ## 5) Corollary: the access barrier is essential -/

/-- WinTruth is Σ₂ for all n,a, and under the standard hypotheses it cannot be uniformly Σ₁. -/
theorem access_barrier_essential :
    (∀ n a, Nonempty (Sigma2Prop (WinTruth n a))) ∧
    ¬(∃ (PATruth : PASentence → Prop),
        OmegaNonComputable ∧
        Nonempty (HaltingSoundness PATruth) ∧
        (∀ n, ∃! a, WinTruth n a) ∧
        Nonempty (UniformlySigma1 PATruth (α := ℕ × Fin 2) WinTruthFamily)) := by
  constructor
  · intro n a
    exact ⟨WinTruth_is_sigma2 n a⟩
  · intro hEx
    rcases hEx with ⟨PATruth, hNon, ⟨hSound⟩, hUnique, ⟨hUnif⟩⟩
    exact WinTruth_not_uniformly_sigma1 (PATruth := PATruth) hNon hSound hUnique hUnif

end RevHalt.Instances.PA
