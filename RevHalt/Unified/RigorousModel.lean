import RevHalt
import Mathlib.Data.Set.Basic

namespace RevHalt_Unified

-- ==============================================================================================
-- Part F: Rigorous Foundational Model with Coherence Conditions
-- ==============================================================================================

/-!
## Final Foundational Fixes

**All issues fixed**:
1. ✓ CCHalts := ∃ n, (Program e n).isSome (not step 0)
2. ✓ compile_halts_equiv proven without sorry
3. ✓ No axiom exec_at_zero
4. ✓ `PredDef : PredCode → Code → Prop` for DEFINABILITY (not Bool decidability)
5. ✓ `no_complement_halts` ensures ¬FMHalts is NOT definable
6. ✓ repr_provable_not uses Prop (representability, not decidability)
-/

/--
**Rigorous Foundational Model**
- Halting = ∃ n, (Program e n).isSome
- PredDef : Prop (definability, not decidability)
- no_complement_halts ensures coherence
-/
structure RigorousModel where
  Code : Type
  /-- Partial function semantics -/
  Program : Code → (ℕ → Option ℕ)
  /-- Codes for DEFINABLE predicates (not necessarily decidable) -/
  PredCode : Type
  /-- Definability relation (Prop, not Bool!) -/
  PredDef : PredCode → Code → Prop
  /-- Diagonal for definable predicates -/
  diagonal_halting : ∀ p : PredCode, ∃ e, (∃ n, (Program e n).isSome) ↔ PredDef p e
  /-- Non-halting code -/
  nonHaltingCode : Code
  nonHalting : ¬∃ n, (Program nonHaltingCode n).isSome
  /-- **COHERENCE CONDITION**: ¬Halts is NOT definable in PredCode -/
  no_complement_halts : ¬∃ pc : PredCode, ∀ e, PredDef pc e ↔ ¬∃ n, (Program e n).isSome

/-- Halting predicate with ∃n semantics. NOT definable as PredCode! -/
def RMHalts (M : RigorousModel) (e : M.Code) : Prop :=
  ∃ n, (M.Program e n).isSome

/-- Compile from Program. -/
def rmCompile (M : RigorousModel) (e : M.Code) : Trace :=
  fun n => ∃ k, k ≤ n ∧ (M.Program e k).isSome

/-- **PROVEN WITHOUT SORRY**: Halts(compile e) ↔ RMHalts e -/
theorem rm_compile_halts_equiv (M : RigorousModel) (e : M.Code) :
    Halts (rmCompile M e) ↔ RMHalts M e := by
  constructor
  · intro ⟨n, hn⟩; obtain ⟨k, _, hk⟩ := hn; exact ⟨k, hk⟩
  · intro ⟨k, hk⟩; exact ⟨k, k, le_refl k, hk⟩

/-- Diagonal for definable predicates. -/
theorem rm_diagonal_def (M : RigorousModel)
    (P : M.Code → Prop)
    (h_def : ∃ p : M.PredCode, ∀ e, M.PredDef p e ↔ P e) :
    ∃ e, RMHalts M e ↔ P e := by
  obtain ⟨p, hp⟩ := h_def
  obtain ⟨e, he⟩ := M.diagonal_halting p
  use e
  simp only [RMHalts]
  constructor
  · intro h; exact (hp e).mp (he.mp h)
  · intro h; exact he.mpr ((hp e).mpr h)

/--
**Coherence Theorem**: No predicate equivalent to ¬RMHalts can exist.
This is PROVEN from no_complement_halts.
-/
theorem no_anti_halting (M : RigorousModel) :
    ¬∃ P : M.Code → Prop, (∃ p : M.PredCode, ∀ e, M.PredDef p e ↔ P e) ∧
                          (∀ e, P e ↔ ¬RMHalts M e) := by
  intro ⟨P, ⟨p, hp⟩, hP⟩
  apply M.no_complement_halts
  use p
  intro e
  rw [hp e, hP e]
  simp only [RMHalts]

/--
**Sound Logic Definition** (Pure Logic - NO dependency on RigorousModel)
Uses Prop for representability (not Bool), avoiding decidability assumption.
-/
structure SoundLogicDef (PropT : Type) where
  /-- Derivability (syntactic) -/
  Provable : PropT → Prop
  /-- Truth (semantic) -/
  Truth : PropT → Prop
  /-- Soundness: derivable implies true -/
  soundness : ∀ p, Provable p → Truth p
  /-- Negation -/
  Not : PropT → PropT
  /-- False proposition -/
  FalseP : PropT
  /-- Consistency -/
  consistent : ¬Provable FalseP
  /-- Absurdity from contradiction -/
  absurd : ∀ p, Provable p → Provable (Not p) → Provable FalseP
  /-- Classical negation for Truth -/
  truth_not_iff : ∀ p, Truth (Not p) ↔ ¬Truth p

/--
**Arithmetization Hypothesis** (Bridge between M and L)
Captures the Gödelian representability of "Provable(Not(G e))" in the definability system.
This is SEPARATE from pure logic.
-/
structure Arithmetization (M : RigorousModel) (PropT : Type) (L : SoundLogicDef PropT) where
  /-- **KEY**: Provable(Not(G e)) is DEFINABLE (not decidable) for any G -/
  repr_provable_not : ∀ G : M.Code → PropT, ∃ pc : M.PredCode,
    ∀ e, M.PredDef pc e ↔ L.Provable (L.Not (G e))

/--
**Build TuringGodelContext'** from Model(M), Kit(K), Logic(L), and Arithmetization(A).
-/
def TGContext_from_RM
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicDef PropT)
    (A : Arithmetization M PropT L) :
    TuringGodelContext' M.Code PropT where
  RealHalts := fun e => Rev0_K K (rmCompile M e)
  Provable := L.Provable
  FalseT := L.FalseP
  Not := L.Not
  consistent := L.consistent
  absurd := L.absurd
  diagonal_program := by
    intro G
    obtain ⟨pc, hpc⟩ := A.repr_provable_not G
    obtain ⟨e, he⟩ := M.diagonal_halting pc
    use e
    rw [T1_traces K hK (rmCompile M e)]
    rw [rm_compile_halts_equiv M e]
    simp only [RMHalts]
    constructor
    · intro hHalts; exact (hpc e).mp (he.mp hHalts)
    · intro hProv; exact he.mpr ((hpc e).mpr hProv)

/-- **Master Theorem from Rigorous Model**: No sorry, no axiom, coherence proven! -/
theorem RevHalt_Master_Rigorous
    {PropT : Type}
    (M : RigorousModel)
    (K : RHKit) (hK : DetectsMonotone K)
    (L : SoundLogicDef PropT)
    (A : Arithmetization M PropT L) :
    (∀ G : M.Code → PropT, ∃ e, Rev0_K K (rmCompile M e) ↔ L.Provable (L.Not (G e))) := by
  intro G
  exact (TGContext_from_RM M K hK L A).diagonal_program G

end RevHalt_Unified
