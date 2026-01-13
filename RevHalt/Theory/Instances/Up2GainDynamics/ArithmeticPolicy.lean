import RevHalt.Theory.Instances.Up2GainDynamics
import RevHalt.Theory.Instances.Up2GainDynamics.Drift

namespace RevHalt
namespace Up2GainDynamics

open Set
open RevHalt.Up2Gain

/-!
  ============================
  Arithmetic Bridge for Drift (Ask n entry mechanism)
  ============================
-/

/-- Il existe un certificat de victoire “externe” pour l’index n, présent dans la frontière S1. -/
def WinFrontierAt (Γ : Set Pos) (n : ℕ) : Prop :=
  ∃ L g m : ℕ, Pos.ProvideWin L n g m ∈ S1 Γ

/--
  Fundamental lemma: in a Cn-closed set,
  not provable is exactly not member.

  This is valid because Cn Γ = { p | Provable Γ p }.
-/
@[simp] lemma mem_Cn_iff (Γ : Set Pos) (p : Pos) : p ∈ Cn Γ ↔ Provable Γ p := Iff.rfl

lemma notProvable_iff_not_mem_of_cn_closed
    (Γ : Set Pos) (hClosed : Cn Γ = Γ) (p : Pos) :
    (¬ Provable Γ p) ↔ p ∉ Γ := by
  constructor
  · intro hNprov hpMem
    -- hpMem : p ∈ Γ
    -- hClosed : Cn Γ = Γ.
    -- We want Provable Γ p, which means p ∈ Cn Γ.
    have hpCn : p ∈ Cn Γ := by
      rw [hClosed]
      exact hpMem
    -- p ∈ Cn Γ means Provable Γ p
    have hpProv : Provable Γ p := (mem_Cn_iff _ _).1 hpCn
    exact hNprov hpProv
  · intro hNotMem hpProv
    -- hpProv : Provable Γ p means p ∈ Cn Γ
    have hpCn : p ∈ Cn Γ := (mem_Cn_iff _ _).2 hpProv
    -- We want p ∈ Γ. Since Cn Γ = Γ, we rewrite Γ to Cn Γ.
    have hpMem : p ∈ Γ := by
      rw [← hClosed]
      exact hpCn
    exact hNotMem hpMem

/--
  Arithmetic Win with Freshness:
  There is a valid arithmetic window with sufficient gain,
  and the corresponding ProvideWin statement is NOT yet in Γ.

  Note: This is "Arithmetic + Structural Freshness".
  The freshness condition (∉ Γ) depends on the dynamic stage Γ.
-/
def ArithWinFreshAt (Γ : Set Pos) (n : ℕ) : Prop :=
  ∃ L g m : ℕ,
    Window L n g m ∧ g ≥ 2 * L + 1 ∧
    Pos.ProvideWin L n g m ∉ Γ

/--
  Bridging Lemma:
  WinFrontierAt (structural) <-> ArithWinFreshAt (arithmetic)
  given closure.
-/
lemma winFrontierAt_iff_arithWinFreshAt
    (Γ : Set Pos) (hClosed : Cn Γ = Γ) (n : ℕ) :
    WinFrontierAt Γ n ↔ ArithWinFreshAt Γ n := by
  -- WinFrontierAt Γ n := ∃ L g m, ProvideWin L n g m ∈ S1 Γ
  -- S1 Γ = {p | isGood p ∧ ¬Provable Γ p}
  -- isGood(ProvideWin ...) ↔ Window ... ∧ g ≥ 2L+1
  -- ¬Provable ↔ not_mem via hClosed
  constructor
  · rintro ⟨L, g, m, hS1⟩
    have : isGood (Pos.ProvideWin L n g m) ∧ ¬ Provable Γ (Pos.ProvideWin L n g m) := by
      -- unfold S1 via lemma
      simpa [S1_eq_good_notProvable] using hS1
    rcases this with ⟨hGood, hNprov⟩
    -- hGood simplifies to Window ∧ threshold
    -- hNprov converts to "∉ Γ" via closure
    have hNotMem : Pos.ProvideWin L n g m ∉ Γ :=
      (notProvable_iff_not_mem_of_cn_closed Γ hClosed _).1 hNprov
    -- extract Window + threshold from isGood
    have hWin : Window L n g m ∧ g ≥ 2 * L + 1 := by
      simpa [isGood] using hGood
    exact ⟨L, g, m, hWin.1, hWin.2, hNotMem⟩
  · rintro ⟨L, g, m, hW, hThresh, hNotMem⟩
    -- construct proof of ∈ S1 Γ
    have hGood : isGood (Pos.ProvideWin L n g m) := by
      simpa [isGood] using And.intro hW hThresh
    have hNprov : ¬ Provable Γ (Pos.ProvideWin L n g m) :=
      (notProvable_iff_not_mem_of_cn_closed Γ hClosed _).2 hNotMem
    -- lift to S1
    refine ⟨L, g, m, ?_⟩
    simpa [S1_eq_good_notProvable] using And.intro hGood hNprov

/--
  Direct API: Produce an S1 element from Arithmetic Freshness.
  Useful for injecting witnesses directly without unfolding existentials.

  [CLEANUP] Removed the existential detour as requested.
-/
lemma provideWin_mem_S1_of_arithWinFreshAt
    (Γ : Set Pos) (hClosed : Cn Γ = Γ)
    (L n g m : ℕ)
    (hWin : Window L n g m)
    (hThresh : g ≥ 2 * L + 1)
    (hFresh : Pos.ProvideWin L n g m ∉ Γ) :
    Pos.ProvideWin L n g m ∈ S1 Γ := by
  -- Direct proof:
  have hGood : isGood (Pos.ProvideWin L n g m) := by
    simpa [isGood] using And.intro hWin hThresh
  have hNprov : ¬ Provable Γ (Pos.ProvideWin L n g m) :=
    (notProvable_iff_not_mem_of_cn_closed Γ hClosed _).2 hFresh
  simpa [S1_eq_good_notProvable] using And.intro hGood hNprov


/-- (A) Si un `ProvideWin L n g m` est axiome, alors `Ask n` est dans `Cn`. -/
lemma ask_mem_Cn_of_provideWin_mem (Γ : Set Pos) (L n g m : ℕ)
    (h : Pos.ProvideWin L n g m ∈ Γ) :
    Pos.Ask n ∈ Cn Γ := by
  -- membership in Cn = Provable
  show Provable Γ (Pos.Ask n)
  intro S hS
  have hWin : S (Pos.ProvideWin L n g m) := hS.1 _ h

  -- Step n est prouvé via le coup P vers ProvideWin L n g m
  have hStep : S (Pos.Step n) := by
    have hMove : (∃ q, pCanMove (Pos.Step n) q ∧ S q) := by
      refine ⟨Pos.ProvideWin L n g m, ?_, hWin⟩
      -- pCanMove (Step n) (ProvideWin L n g m)
      -- se prouve par la branche ∃ L g m, q = ProvideWin L n g m
      dsimp [pCanMove]
      exact Or.inr ⟨L, g, m, rfl⟩
    exact hS.2.1 (Pos.Step n) (by simp [turnFn]) hMove

  -- Ask n est prouvé via le coup P vers Step n
  have hMoveAsk : (∃ q, pCanMove (Pos.Ask n) q ∧ S q) := by
    refine ⟨Pos.Step n, ?_, hStep⟩
    -- pCanMove (Ask n) (Step n)
    simp [pCanMove]
  exact hS.2.1 (Pos.Ask n) (by simp [turnFn]) hMoveAsk

/-- (B) Si `WinFrontierAt (Γ_k) n` est vrai, alors `Ask n` est vrai au stade k+1/step. -/
lemma ask_mem_stage_succ_of_winFrontier (Γ0 : Set Pos) (k n : ℕ)
    (hW : WinFrontierAt ((A Γ0 k).Γ) n) :
    Pos.Ask n ∈ (A Γ0 (k+1)).Γ := by
  rcases hW with ⟨L, g, m, hS1⟩
  -- réécrire A_{k+1}
  rw [A_succ (Γ0 := Γ0) (n := k)]
  -- exposer la définition : Γ(step A_k) = Cn (Γ_k ∪ S1 Γ_k)
  simp only [step, RevHalt.FState, RevHalt.F]

  -- il suffit de prouver Ask n ∈ Cn (Γ_k ∪ S1 Γ_k)
  -- en utilisant que ProvideWin L n g m est dans S1 Γ_k donc dans l’union
  have hUnion : Pos.ProvideWin L n g m ∈ ((A Γ0 k).Γ ∪ S1 ((A Γ0 k).Γ)) :=
    Or.inr hS1

  exact ask_mem_Cn_of_provideWin_mem
    (Γ := (A Γ0 k).Γ ∪ S1 ((A Γ0 k).Γ)) (L := L) (n := n) (g := g) (m := m) hUnion

/-- (C) Propriété de "couverture progressive" par des gains. -/
def ProgressiveWins (Γ0 : Set Pos) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, WinFrontierAt ((A Γ0 k).Γ) n

/-- Hypothèse séquentielle : à chaque étape k, on obtient un win pour `schedule k`. -/
def StepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, WinFrontierAt ((A Γ0 k).Γ) (schedule k)

/-- Fairness (couverture) : chaque n apparaît à un certain rang dans `schedule`. -/
def FairSchedule (schedule : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, schedule k = n

/-- StepwiseWins + fairness ⇒ ProgressiveWins. -/
lemma progressiveWins_of_stepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule) :
    ProgressiveWins Γ0 := by
  intro n
  rcases hFair n with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  -- hStep k : WinFrontierAt ((A Γ0 k).Γ) (schedule k)
  simpa [hk] using hStep k

/-- ProgressiveWins implies eventually finding Ask n. -/
lemma progressive_asks_of_progressiveWins (Γ0 : Set Pos)
    (hProg : ProgressiveWins Γ0) :
    ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ := by
  intro n
  rcases hProg n with ⟨k, hW⟩
  refine ⟨k+1, ?_⟩
  exact ask_mem_stage_succ_of_winFrontier Γ0 k n hW

/-- Version robuste de `progressive_asks` : dérivée d’un win par étape + fairness. -/
lemma progressive_asks_of_stepwiseWins (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule) :
    ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ := by
  -- recycle ton lemme existant
  exact progressive_asks_of_progressiveWins Γ0
    (progressiveWins_of_stepwiseWins (Γ0 := Γ0) (schedule := schedule) hStep hFair)

/-- Conséquence finale : Option B (Drift) sans axiome global, via stepwise + fairness. -/
theorem optionB_drift_counterexample_stepwise (Γ0 : Set Pos) (schedule : ℕ → ℕ)
    (hStep : StepwiseWins Γ0 schedule)
    (hFair : FairSchedule schedule)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) := by
  -- 1) tous les Ask n entrent (à des temps éventuellement différents)
  have hAskA : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (A Γ0 k).Γ :=
    progressive_asks_of_stepwiseWins (Γ0 := Γ0) (schedule := schedule) hStep hFair

  -- 2) réexprimer en termes de `chain` pour utiliser le lemme drift déjà prouvé
  have hAsk : ∀ n : ℕ, ∃ k : ℕ, Pos.Ask n ∈ (chain Γ0 k).Γ := by
    intro n
    rcases hAskA n with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [chain, A] using hk

  -- 3) appliquer le drift générique
  exact drift_not_OmegaAdmissible_ωΓ_of_progressive_asks Γ0 hAsk hRoot

-- ==============================================================================================
-- CANONICAL POLICY (Standard Verification Strategy)
-- ==============================================================================================

/-!
  ## Canonical Policy
  We define a concrete, constructive schedule to demonstrate that `FairSchedule` is inhabited
  and easily realizable.

  The "Standard Schedule" simply targets integer `k` at step `k`.
  Use case: The verifier systematically checks n=0, n=1, n=2...
-/

/-- Standard Schedule: at step k, we target n = k. -/
def StandardSchedule : ℕ → ℕ := id

/-- The Standard Schedule is fair (it covers every integer). -/
lemma standardSchedule_fair : FairSchedule StandardSchedule := by
  intro n
  use n
  rfl

/--
  **Diagonal Arithmetic Wins**:
  For every step `n`, there exists a valid, fresh arithmetic window targeting `n`.
-/
def DiagonalArithWins (Γ0 : Set Pos) : Prop :=
  ∀ n : ℕ, ArithWinFreshAt ((A Γ0 n).Γ) n

/-- DiagonalArithWins implies StepwiseWins (on StandardSchedule). -/
lemma stepwiseWins_of_diagonalArithWins (Γ0 : Set Pos)
    (hDiag : DiagonalArithWins Γ0) :
    StepwiseWins Γ0 StandardSchedule := by
  intro n
  -- StandardSchedule n = n
  unfold StandardSchedule; simp
  have hClosed : Cn ((A Γ0 n).Γ) = (A Γ0 n).Γ := (A Γ0 n).cn_closed
  -- convert arithmetic win to structural win
  rw [winFrontierAt_iff_arithWinFreshAt ((A Γ0 n).Γ) hClosed n]
  exact hDiag n

/--
  **Canonical Drift Theorem** (Arithmetic Version):
  If we can produce a fresh arithmetic window for every `n` at step `n` (Diagonal Wins),
  then the system drifts into Option B (structural incompleteness at ω).

  This is the fully constructive target for the Collatz analysis.
-/
theorem canonical_drift_counterexample
    (Γ0 : Set Pos)
    (hDiagWins : DiagonalArithWins Γ0)
    (hRoot : ∀ k : ℕ, Pos.Root ∉ (chain Γ0 k).Γ) :
    ¬ RevHalt.OmegaAdmissible (PropT := Pos) (Provable := Provable) (Cn := Cn) (ωΓ Γ0) := by
  apply optionB_drift_counterexample_stepwise Γ0 StandardSchedule
  · exact stepwiseWins_of_diagonalArithWins Γ0 hDiagWins
  · exact standardSchedule_fair
  · exact hRoot


end Up2GainDynamics
end RevHalt
