import RevHalt.Theory.Up2Gain
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Function.Iterate

namespace RevHalt
namespace Up2GainWindows

open RevHalt.Up2Gain
open scoped BigOperators

/-
  ============================================================
  0) Accessors “structuraux” (évite les simp fragiles)
  ============================================================
-/

@[simp] lemma isValidWindow_tag
    {L : ℕ} {c : WindowCert L} (hV : IsValidWindow L c) (i : Fin L) :
    c.tags i = tag (c.states (Fin.castSucc i)) :=
  hV.1 i

@[simp] lemma isValidWindow_state_step
    {L : ℕ} {c : WindowCert L} (hV : IsValidWindow L c) (i : Fin L) :
    c.states (Fin.succ i) = shortcut (c.states (Fin.castSucc i)) :=
  hV.2 i

/-
  ============================================================
  1) Constructeur canonique : “la fenêtre standard de longueur L”
     - states i = shortcut^i n
     - tags i   = tag(states i)
  ============================================================
-/

/-- Itération (sur ℕ) de shortcut. -/
def iterShortcut (k : ℕ) (n : ℕ) : ℕ :=
  Nat.iterate shortcut k n

/-- Certificat canonique : suit la trajectoire `shortcut` à partir de `n`. -/
def mkWindowCert (L : ℕ) (n : ℕ) : WindowCert L where
  states := fun i => iterShortcut i.1 n
  tags   := fun i => tag (iterShortcut i.1 n)

/-- Lemma utilitaire : `iterate` commute au “un pas” (forme f(f^n x)). -/
lemma iterate_succ_eq (f : α → α) (k : ℕ) (x : α) :
    Nat.iterate f (k+1) x = f (Nat.iterate f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.iterate] at *
    rw [ih]

/-- Le certificat canonique est une fenêtre valide. -/
lemma isValid_mkWindowCert (L : ℕ) (n : ℕ) :
    IsValidWindow L (mkWindowCert L n) := by
  refine ⟨?tagsOK, ?stepOK⟩
  · intro i
    -- tags i = tag(states castSucc i) par définition
    simp [mkWindowCert, iterShortcut]
  · intro i
    -- states (succ i) = shortcut(states (castSucc i))
    -- via `iterate_succ_eq` et le fait que (succ i).val = i.val+1
    have : iterShortcut (i.1 + 1) n = shortcut (iterShortcut i.1 n) := by
      simpa [iterShortcut, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using (iterate_succ_eq (f := shortcut) (k := i.1) (x := n))
    simpa [mkWindowCert, iterShortcut] using this

@[simp] lemma mkWindowCert_state_zero (L : ℕ) (n : ℕ) :
    (mkWindowCert L n).states 0 = n := by
  simp [mkWindowCert, iterShortcut]

@[simp] lemma mkWindowCert_state_last (L : ℕ) (n : ℕ) :
    (mkWindowCert L n).states (Fin.last L) = iterShortcut L n := by
  -- `Fin.last L` a pour valeur `L`
  simp [mkWindowCert, iterShortcut]

/-- Fenêtre canonique : fournit directement un témoin de `Window`. -/
lemma window_mkWindowCert (L : ℕ) (n : ℕ) :
    Window L n (sumTags (mkWindowCert L n).tags) ((mkWindowCert L n).states (Fin.last L)) := by
  refine ⟨mkWindowCert L n, isValid_mkWindowCert L n, ?_, ?_, rfl⟩
  · simp [mkWindowCert_state_zero L n]
  · rfl

/-
  ============================================================
  2) Normalisation du gain g : somme des tags = somme des tag(states)
  ============================================================
-/

/-- Pont : `sumTags` vu comme somme finie. -/
lemma sumTags_eq_sum {L : ℕ} (t : Fin L → ℕ) :
    sumTags t = (∑ i : Fin L, t i) := by
  -- P i : sumTagsAux L t i acc = acc + \sum_{j >= i} t j
  let P (i : ℕ) := ∀ acc, sumTagsAux L t i acc = acc + ∑ j : Fin L, if i ≤ j.1 then t j else 0

  -- Step Logic: P (i+1) -> P i
  have h_step : ∀ i < L, P (i + 1) → P i := by
    intro i hi ih acc
    rw [sumTagsAux]
    simp [hi]
    rw [ih (acc + t ⟨i, hi⟩)]
    simp [Nat.add_assoc]
    -- Goal: t i + S_{i+1} = S_i
    -- RHS = S_i = t i + S_{i+1}
    let S (k : ℕ) := ∑ j : Fin L, if k ≤ j.1 then t j else 0
    change t ⟨i, hi⟩ + S (i + 1) = S i
    dsimp [S]
    -- Decompose RHS S i at i
    rw [← @Finset.add_sum_erase (Fin L) ℕ _ _ Finset.univ (fun j => if i ≤ j.1 then t j else 0) ⟨i, hi⟩ (Finset.mem_univ _)]
    -- Decompose LHS S (i+1) at i (term is 0)
    rw [← @Finset.add_sum_erase (Fin L) ℕ _ _ Finset.univ (fun j => if i+1 ≤ j.1 then t j else 0) ⟨i, hi⟩ (Finset.mem_univ _)]
    simp only [Nat.not_succ_le_self, if_false, zero_add]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      have h_ne : j ≠ ⟨i, hi⟩ := Finset.mem_erase.mp hj |>.1
      have h_val_ne : j.1 ≠ i := fun h => h_ne (Fin.eq_of_val_eq h)
      -- For j != i: i <= j <-> i < j <-> i+1 <= j
      refine if_congr ?_ rfl rfl
      rw [Nat.succ_le_iff]
      rw [le_iff_eq_or_lt]
      simp [Ne.symm h_val_ne]

  -- Manual induction on k = L - i
  have h_ind : ∀ k, ∀ i, L - i = k → P i := by
    intro k
    induction k with
    | zero =>
      intro i h_len
      have hi : L ≤ i := Nat.le_of_sub_eq_zero h_len
      -- Base case P i for i >= L
      intro acc
      rw [sumTagsAux]
      simp [Nat.not_lt_of_le hi]
      -- RHS sum is 0 because i <= j is always false for j < L <= i
      have h_empty : ∀ j : Fin L, ¬ (i ≤ j.1) := fun j => Nat.not_le_of_gt (Nat.lt_of_lt_of_le j.2 hi)
      simp [h_empty]
    | succ k ih =>
      intro i h_len
      -- L - i = k + 1 implies i < L
      have hi : i < L := by
        apply Nat.lt_of_sub_eq_succ h_len
      -- Apply step with IH
      apply h_step i hi
      apply ih (i + 1)
      -- Check measure: L - (i + 1) = k
      rw [Nat.sub_succ, h_len]
      rfl

  -- Apply to i=0
  have h_0 := h_ind L 0 (Nat.sub_zero L) 0
  simp at h_0
  unfold sumTags
  rw [h_0]


/-- Dans une fenêtre valide, `sumTags tags` = somme des `tag(states i)` (i < L). -/
lemma sumTags_eq_sum_tag_states
    {L : ℕ} {c : WindowCert L} (hV : IsValidWindow L c) :
    sumTags c.tags = sumTags (fun i : Fin L => tag (c.states (Fin.castSucc i))) := by
  -- par extensionalité sur `tags`, puis réécriture
  have ht : c.tags = (fun i : Fin L => tag (c.states (Fin.castSucc i))) := by
    funext i
    simpa using (isValidWindow_tag (c := c) hV i)
  simp [ht]

/-
  ============================================================
  3) Lemmes de seuil sur `sumTags`
     Objectif : produire `g ≥ 2*L+1` via bornes sur les tags.
  ============================================================
-/

/-- Borne inférieure générique : si tous les termes ≥ a, la somme ≥ a*L. -/
lemma sumTags_ge_mul_of_forall_ge
    (a : ℕ) {L : ℕ} (t : Fin L → ℕ) (h : ∀ i, a ≤ t i) :
    a * L ≤ sumTags t := by
  -- preuve par induction sur L en utilisant `Fin.sum_univ_succ`
  rw [sumTags_eq_sum]
  classical
  induction L with
  | zero =>
      simp
  | succ L ih =>
      -- réécrire la somme sur Fin (L+1)
      have ih' : a * L ≤ ∑ i : Fin L, t i.castSucc := by
        apply ih
        intro i
        simpa using h i.castSucc
      -- somme = somme(castSucc) + dernier
      -- et dernier ≥ a
      have hLast : a ≤ t (Fin.last L) := h (Fin.last L)
      -- passer via la forme Σ
      simp [Fin.sum_univ_castSucc, Nat.mul_succ]
      -- Après simp, le but devient: a*L + a ≤ (∑ i : Fin L, t i.castSucc) + t (Fin.last L)
      exact Nat.add_le_add ih' hLast

/--
Critère “propre” pour obtenir `2*(k+1)+1` :
- tous les tags des k premiers pas sont ≥ 2
- le tag du dernier pas est ≥ 3
Donc somme ≥ 2k + 3 = 2*(k+1)+1.
-/
lemma two_mul_succ_add_one_le_sumTags_of_last_ge_three
    (k : ℕ) (t : Fin (k+1) → ℕ)
    (h2 : ∀ i : Fin k, 2 ≤ t i.castSucc)
    (hLast : 3 ≤ t (Fin.last k)) :
    2 * (k+1) + 1 ≤ sumTags t := by
  rw [sumTags_eq_sum]
  classical
  -- Décomposer la somme sur Fin (k+1) = Fin k + dernier
  have hFirst : 2 * k ≤ ∑ i : Fin k, t i.castSucc := by
    -- `2*k ≤ sumTags` via le lemme générique (mais sur Finset.sum)
    rw [← sumTags_eq_sum]
    apply sumTags_ge_mul_of_forall_ge (a := 2)
    intro i
    exact h2 i

  -- Puis ajouter le dernier terme ≥ 3
  -- et réécrire `sumTags t` comme somme(first) + last
  -- (via `Fin.sum_univ_succ`)
  rw [Fin.sum_univ_castSucc]
  simp only [Nat.mul_succ]
  rw [Nat.add_assoc, Nat.add_zero]
  -- Goal: 2 * k + 3 ≤ ...
  -- hFirst : 2 * k ≤ sum ...
  -- hLast : 3 ≤ last
  exact Nat.add_le_add hFirst hLast

/-
  ============================================================
  4) “Packaging” pour Window : version utilisable directement
  ============================================================
-/

/--
Version pratique : si `Window (k+1) n g m` est témoin par un cert c,
et si les tags de c satisfont le critère (≥2 partout, ≥3 sur le dernier),
alors g ≥ 2*(k+1)+1.

C’est le point d’entrée typique pour la partie arithmétique :
vous prouvez des bornes sur `tag (states ...)` puis vous translatez sur `tags`.
-/
theorem window_threshold_of_tags
    {k n g m : ℕ}
    (hW : Window (k+1) n g m)
    (h2 : ∀ c : WindowCert (k+1), IsValidWindow (k+1) c → c.states 0 = n →
            (∀ i : Fin k, 2 ≤ c.tags i.castSucc))
    (hLast : ∀ c : WindowCert (k+1), IsValidWindow (k+1) c → c.states 0 = n →
            3 ≤ c.tags (Fin.last k)) :
    2 * (k+1) + 1 ≤ g := by
  rcases hW with ⟨c, hV, h0, hM, hG⟩
  -- On remplace g par sumTags c.tags
  subst h0
  -- g = sumTags c.tags
  have : 2 * (k+1) + 1 ≤ sumTags c.tags := by
    apply two_mul_succ_add_one_le_sumTags_of_last_ge_three (k := k) (t := c.tags)
    · intro i
      exact h2 c hV rfl i
    · exact hLast c hV rfl
  simpa [hG] using this

end Up2GainWindows
end RevHalt
