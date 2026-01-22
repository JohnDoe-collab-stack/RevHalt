import RevHalt.Theory.Complementarity
import RevHalt.Theory.Impossibility
import RevHalt.Theory.Stabilization

namespace RevHalt

open Nat.Partrec

/-!
### Quantification constructive (sans Classical, sans noncomputable)

On ne cherche pas un "minimum global" (non constructif en général).
On introduit un modèle de coût paramétrique sur les certificats contenus dans `OraclePick`,
puis on définit une difficulté locale `Code → Nat` relative à un choix `picks`.
-/

/-- Modèle de coût : mesure d’un certificat positif/négatif (au sens `OraclePick`). -/
structure PickCostModel {Code PropT : Type}
    (S : ComplementaritySystem Code PropT) where
  cost_pos : ∀ e : Code, Rev0_K S.K (S.Machine e) → Nat
  cost_neg : ∀ e : Code, KitStabilizes S.K (S.Machine e) → Nat

/-- Coût d’un `OraclePick` (définition pure, donc constructive). -/
def oraclePickCost
    {Code PropT : Type}
    {S : ComplementaritySystem Code PropT}
    (encode_halt encode_not_halt : Code → PropT)
    (M : PickCostModel S)
    {e : Code}
    (pick : OraclePick S encode_halt encode_not_halt e) : Nat := by
  -- Robust matching for both PSum (current) or Or (legacy variant)
  cases pick.cert with
  | inl h => exact M.cost_pos e h.1
  | inr h => exact M.cost_neg e h.1

/-- Fonction de difficulté locale : `e ↦ coût(picks e)` (relative au choix `picks`). -/
def localDifficulty
    {Code PropT : Type}
    {S : ComplementaritySystem Code PropT}
    (encode_halt encode_not_halt : Code → PropT)
    (M : PickCostModel S)
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    Code → Nat :=
  fun e => oraclePickCost (S:=S) encode_halt encode_not_halt M (picks e)

/-- Variante utile : une borne "il existe un pick de coût ≤ n". -/
def DifficultyBound
    {Code PropT : Type}
    (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (M : PickCostModel S)
    (e : Code) (n : Nat) : Prop :=
  ∃ pick : OraclePick S encode_halt encode_not_halt e,
    oraclePickCost (S:=S) encode_halt encode_not_halt M pick ≤ n

/-- Un choix `picks` produit immédiatement une borne (constructive). -/
theorem DifficultyBound_of_picks
    {Code PropT : Type}
    (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (M : PickCostModel S)
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    ∀ e, DifficultyBound S encode_halt encode_not_halt M e
      (localDifficulty (S:=S) encode_halt encode_not_halt M picks e) := by
  intro e
  refine ⟨picks e, ?_⟩
  -- coût(picks e) ≤ coût(picks e)
  exact Nat.le_refl _

/-- La borne de difficulté est monotone (utile pour les preuves de bornes supérieures). -/
theorem DifficultyBound_mono
    {Code PropT : Type}
    (S : ComplementaritySystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT)
    (M : PickCostModel S)
    (e : Code) {n m : Nat} :
    DifficultyBound S encode_halt encode_not_halt M e n →
    n ≤ m →
    DifficultyBound S encode_halt encode_not_halt M e m := by
  intro h hn
  rcases h with ⟨pick, hle⟩
  exact ⟨pick, Nat.le_trans hle hn⟩

/-
Ton théorème T3 original est déjà constructif : il ne demande ni `Classical` ni `noncomputable`.
On ne le modifie pas, on ajoute une version "quantifiée" qui expose un coût Nat via `DifficultyBound`.
-/
theorem T3_permits_instancewise
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (e : Code)
    (pick : OraclePick S encode_halt encode_not_halt e) :
    ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧
      (∀ p ∈ S_e, Truth p) ∧
      (pick.p ∈ S_e) ∧
      ((pick.p = encode_halt e) ∨ (pick.p = encode_not_halt e)) := by
  let S_e : Set PropT := S2 ∪ {pick.p}

  have hTruthPick : Truth pick.p := by
    cases pick.cert with
    | inl h =>
        have hKit : Rev0_K S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_halt e := h.2
        rw [hpEq]
        exact h_pos e hKit
    | inr h =>
        have hNotKit : KitStabilizes S.K (S.Machine e) := h.1
        have hpEq : pick.p = encode_not_halt e := h.2
        rw [hpEq]
        exact h_neg e hNotKit

  have hPickForm : (pick.p = encode_halt e) ∨ (pick.p = encode_not_halt e) := by
    cases pick.cert with
    | inl h => exact Or.inl h.2
    | inr h => exact Or.inr h.2

  refine ⟨S_e, ?_, ?_, ?_, hPickForm⟩
  · intro p hp; exact Or.inl hp
  · intro p hp
    cases hp with
    | inl hp2 => exact h_S2_sound p hp2
    | inr hpick =>
        have hpEq : p = pick.p := hpick
        rw [hpEq]
        exact hTruthPick
  · exact Or.inr rfl

/-- Version quantifiée : on retourne une `DifficultyBound` formelle, pas juste une égalité. -/
theorem T3_permits_instancewise_quantified
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (M : PickCostModel S)
    (e : Code)
    (pick : OraclePick S encode_halt encode_not_halt e) :
    ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧
      (∀ p ∈ S_e, Truth p) ∧
      (pick.p ∈ S_e) ∧
      ((pick.p = encode_halt e) ∨ (pick.p = encode_not_halt e)) ∧
      DifficultyBound S encode_halt encode_not_halt M e
        (oraclePickCost (S:=S) encode_halt encode_not_halt M pick) := by
  rcases T3_permits_instancewise (S:=S) (Truth:=Truth) (S2:=S2)
      h_S2_sound (encode_halt:=encode_halt) (encode_not_halt:=encode_not_halt)
      h_pos h_neg e pick with
    ⟨S_e, hSub, hSound, hMem, hForm⟩
  refine ⟨S_e, hSub, hSound, hMem, hForm, ?_⟩
  refine ⟨pick, ?_⟩
  exact Nat.le_refl _

/-- Coexistence T2 + T3, plus une difficulté `D : Code → Nat` donnant une borne explicite. -/
theorem quantifier_swap_coexistence_quantified
    {Code PropT : Type} (S : ComplementaritySystem Code PropT)
    (Truth : PropT → Prop)
    (S2 : Set PropT)
    (h_S2_sound : ∀ p ∈ S2, Truth p)
    (encode_halt encode_not_halt : Code → PropT)
    (h_pos : ∀ e, Rev0_K S.K (S.Machine e) → Truth (encode_halt e))
    (h_neg : ∀ e, KitStabilizes S.K (S.Machine e) → Truth (encode_not_halt e))
    (M : PickCostModel S)
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    (¬ Nonempty (InternalHaltingPredicate S.toImpossibleSystem S.K)) ∧
    (∀ e, ∃ S_e : Set PropT,
      S2 ⊆ S_e ∧ (∀ p ∈ S_e, Truth p) ∧ ((picks e).p ∈ S_e)) ∧
    (∃ D : Code → Nat,
      (D = localDifficulty (S:=S) encode_halt encode_not_halt M picks) ∧
      (∀ e, DifficultyBound S encode_halt encode_not_halt M e (D e))) := by
  refine ⟨?t2, ?rest⟩
  · exact T2_impossibility S.toImpossibleSystem S.K S.h_canon
  · refine ⟨?t3, ?diff⟩
    · intro e
      rcases T3_permits_instancewise (S:=S) (Truth:=Truth) (S2:=S2)
          h_S2_sound (encode_halt:=encode_halt) (encode_not_halt:=encode_not_halt)
          h_pos h_neg e (picks e) with
        ⟨S_e, hSub, hSound, hMem, _hForm⟩
      exact ⟨S_e, hSub, hSound, hMem⟩
    · refine ⟨localDifficulty (S:=S) encode_halt encode_not_halt M picks, ?_, ?_⟩
      · rfl
      · -- la borne est donnée par le pick choisi
        simpa [localDifficulty] using
          DifficultyBound_of_picks (S:=S) (encode_halt:=encode_halt) (encode_not_halt:=encode_not_halt) M picks

/-!
# RevHalt.Theory.Certificate (Merged content)

This section connects the abstract `PickCostModel` from above
to concrete notions of "Certificate Size".

We define a `CertificateInterface` that requires:
1. Data types for Halting and Stabilization witnesses.
2. Size functions for these witnesses.
3. Extraction functions (Prop → Data) that realize the Kit's verdicts.

This allows us to instantiate the "Difficulty" function with a canonical measure.
-/

/--
Interface for concrete certificates backing the Kit's verdicts.
This transforms the propositional `Rev0_K` / `KitStabilizes` into data-carrying proofs.
-/
structure CertificateInterface {Code PropT : Type} (S : ComplementaritySystem Code PropT) where
  /-- Data type for positive halting witness (e.g., result, step count). -/
  HaltingCert : Code → Type

  /-- Data type for negative stabilization witness (e.g., cycle detection, invariant). -/
  StabilityCert : Code → Type

  /-- Standard measure of certificate complexity. -/
  haltSize : ∀ {e}, HaltingCert e → Nat
  stabSize : ∀ {e}, StabilityCert e → Nat

  /-- Bridge: Truth → Existence of Certificate (Constructive Realization) -/
  extract_halt : ∀ e, Rev0_K S.K (S.Machine e) → HaltingCert e
  extract_stab : ∀ e, KitStabilizes S.K (S.Machine e) → StabilityCert e

/--
Canonical cost model derived from a Certificate Interface.
This links the abstract `PickCostModel` to the concrete certificate sizes.
-/
def CanonicalCostModel {Code PropT : Type}
    {S : ComplementaritySystem Code PropT}
    (CI : CertificateInterface S) : PickCostModel S :=
{
  cost_pos := fun e h => CI.haltSize (CI.extract_halt e h)
  cost_neg := fun e h => CI.stabSize (CI.extract_stab e h)
}

/-!
## Canonical Difficulty
Given a CertificateInterface, the `localDifficulty` becomes a measure of
"Intrinsic Verification Complexity".
-/

def canonicalDifficulty
    {Code PropT : Type}
    {S : ComplementaritySystem Code PropT}
    (CI : CertificateInterface S)
    (encode_halt encode_not_halt : Code → PropT)
    (picks : ∀ e, OraclePick S encode_halt encode_not_halt e) :
    Code → Nat :=
  localDifficulty encode_halt encode_not_halt (CanonicalCostModel CI) picks

/--
**Dominance Principle**:
If we have two choice functions (picks), their associated canonical difficulties
are comparable via their costs.
-/
theorem difficulty_dominance
    {Code PropT : Type}
    {S : ComplementaritySystem Code PropT}
    (CI : CertificateInterface S)
    (encode_halt encode_not_halt : Code → PropT)
    (picks1 picks2 : ∀ e, OraclePick S encode_halt encode_not_halt e)
    (e : Code) :
    let D := CanonicalCostModel CI
    oraclePickCost encode_halt encode_not_halt D (picks1 e) =
    oraclePickCost encode_halt encode_not_halt D (picks2 e) := by

  -- The cost depends only on the *verification nature* (Halt vs Stab), not the pick wrapper,
  -- PROVIDED the Truth implies a UNIQUE certificate type (which it does: Halt xor Stab).
  -- Note: technically picks1 and picks2 might define 'p' differently if encoding is not injective,
  -- but the 'cert' part determines the branch (Pos vs Neg).
  --
  -- Since Halts(e) is a Prop, it is True or False.
  -- If Halts(e), both picks must be .inl (because .inr requires ¬Halts).
  -- If ¬Halts(e), both picks must be .inr.

  -- Let's prove they land in the same branch of the cost model.


  cases picks1 e
  cases picks2 e
  dsimp [oraclePickCost]
  rename_i p1 cert1 p2 cert2
  cases cert1 with
  | inl h1 =>
    cases cert2 with
    | inl h2 => dsimp;
    | inr h2 => exact False.elim (h2.1 h1.1)
  | inr h1 =>
    cases cert2 with
    | inl h2 => exact False.elim (h1.1 h2.1)
    | inr h2 => dsimp;



-- Axiom checks:lis quantifierSwap
#print axioms RevHalt.T3_permits_instancewise
#print axioms RevHalt.T3_permits_instancewise_quantified
#print axioms RevHalt.quantifier_swap_coexistence_quantified
#print axioms RevHalt.difficulty_dominance
