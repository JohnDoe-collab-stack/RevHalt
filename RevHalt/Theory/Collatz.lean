import RevHalt.Theory.Up2Gain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# RevHalt.Theory.Collatz

Concrete Collatz-oriented lemmas connecting the `Up2Gain` certificate layer (`Window`, `tag`, `gain`)
to actual numerical decrease for the accelerated map `shortcut`.

This is meant as a first “real system” stepping stone: once you can produce/cover certificates,
you can turn them into concrete descent facts.
-/

namespace RevHalt.Collatz

open RevHalt.Up2Gain

/-! ## A small lemma library about `Up2Gain.v2` -/

theorem v2_ge_pow_two_mul (k t : ℕ) (ht : 0 < t) : k ≤ v2 (2 ^ k * t) := by
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      have hpos : 0 < 2 ^ (k + 1) * t :=
        Nat.mul_pos (Nat.pow_pos (n := k + 1) (by decide : 0 < 2)) ht
      have hne : 2 ^ (k + 1) * t ≠ 0 := Nat.ne_of_gt hpos
      have hEven : (2 ^ (k + 1) * t) % 2 = 0 := by
        have h2dvd : 2 ∣ 2 ^ (k + 1) * t := by
          refine ⟨2 ^ k * t, ?_⟩
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        exact Nat.mod_eq_zero_of_dvd h2dvd
      have hdiv : (2 ^ (k + 1) * t) / 2 = 2 ^ k * t := by
        calc
          (2 ^ (k + 1) * t) / 2 = ((2 ^ k * 2) * t) / 2 := by
            simp [Nat.pow_succ, Nat.mul_assoc]
          _ = (2 * (2 ^ k * t)) / 2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 2 ^ k * t := by
            simpa using (Nat.mul_div_right (2 ^ k * t) (by decide : 0 < 2))

      have hv2 : v2 (2 ^ (k + 1) * t) = 1 + v2 (2 ^ k * t) := by
        -- Unfold `v2` only on the LHS.
        nth_rw 1 [Up2Gain.v2]
        rw [if_neg hne]
        rw [if_pos hEven]
        rw [hdiv]

      -- close by induction hypothesis
      have : k + 1 ≤ 1 + v2 (2 ^ k * t) := by
        -- `Nat.succ_le_succ ih`, rewritten
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.succ_le_succ ih)
      simpa [hv2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem v2_ge_of_pow_two_dvd {n k : ℕ} (hn : 0 < n) (h : 2 ^ k ∣ n) : k ≤ v2 n := by
  rcases h with ⟨t, rfl⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    subst ht0
    simpa using hn
  exact v2_ge_pow_two_mul k t (Nat.pos_of_ne_zero ht0)

/-! ## Concrete Collatz (accelerated) facts -/

theorem eight_dvd_three_mul_add_one_of_mod8_eq5 {n : ℕ} (h : n % 8 = 5) : 8 ∣ 3 * n + 1 := by
  have hn : n = n % 8 + 8 * (n / 8) := by
    simpa using (Nat.mod_add_div n 8).symm
  refine ⟨3 * (n / 8) + 2, ?_⟩
  -- expand `n` as `n % 8 + 8*(n/8)`, then use `h : n % 8 = 5`
  calc
    3 * n + 1 = 3 * (n % 8 + 8 * (n / 8)) + 1 := by
      exact congrArg (fun x => 3 * x + 1) hn
    _ = 3 * (5 + 8 * (n / 8)) + 1 := by
      exact congrArg (fun r => 3 * (r + 8 * (n / 8)) + 1) h
    _ = 8 * (3 * (n / 8) + 2) := by
      ring_nf

theorem tag_ge_three_of_mod8_eq5 {n : ℕ} (h : n % 8 = 5) : 3 ≤ tag n := by
  have hpos : 0 < 3 * n + 1 := by
    simpa using Nat.succ_pos (3 * n)
  have hdiv : 2 ^ 3 ∣ 3 * n + 1 := by
    simpa using (eight_dvd_three_mul_add_one_of_mod8_eq5 (n := n) h)
  -- `tag n = v2 (3*n + 1)`
  simpa [Up2Gain.tag] using (v2_ge_of_pow_two_dvd (n := 3 * n + 1) (k := 3) hpos hdiv)

theorem oneStepWindow (n : ℕ) : Window 1 n (tag n) (shortcut n) := by
  classical
  let c : WindowCert 1 :=
    { states := Fin.cases n (fun _ => shortcut n)
      tags := fun _ => tag n }
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i
      simp [c]
    · intro i
      fin_cases i
      simp [c]
      change Fin.cases n (fun _ : Fin 1 => shortcut n) ((0 : Fin 1).succ) = shortcut n
      exact Fin.cases_succ (n := 1) (motive := fun _ : Fin 2 => ℕ)
        (zero := n) (succ := fun _ : Fin 1 => shortcut n) (i := (0 : Fin 1))
  · simp [c]
  · -- `Fin.last 1` is defeq `0.succ` in `Fin 2`.
    change Fin.cases n (fun _ : Fin 1 => shortcut n) ((0 : Fin 1).succ) = shortcut n
    exact Fin.cases_succ (n := 1) (motive := fun _ : Fin 2 => ℕ)
      (zero := n) (succ := fun _ : Fin 1 => shortcut n) (i := (0 : Fin 1))
  · simp [Up2Gain.sumTags, Up2Gain.sumTagsAux, c]

theorem oneStepWindow_highGain_of_mod8_eq5 {n : ℕ} (h : n % 8 = 5) :
    Window 1 n (tag n) (shortcut n) ∧ tag n ≥ 2 * 1 + 1 := by
  refine ⟨oneStepWindow n, ?_⟩
  simpa using tag_ge_three_of_mod8_eq5 (n := n) h

private theorem div_le_div_of_denom_le (a d1 d2 : ℕ) (hd : d1 ≤ d2) (hd1 : 0 < d1) :
    a / d2 ≤ a / d1 := by
  -- Let `q := a / d2`. We show `q * d1 ≤ a`, hence `q ≤ a / d1`.
  apply (Nat.le_div_iff_mul_le hd1).2
  have hqd2 : (a / d2) * d2 ≤ a := Nat.div_mul_le_self a d2
  have hqd1 : (a / d2) * d1 ≤ (a / d2) * d2 := Nat.mul_le_mul_left (a / d2) hd
  exact le_trans hqd1 hqd2

theorem shortcut_lt_of_mod8_eq5 {n : ℕ} (h : n % 8 = 5) : shortcut n < n := by
  have hn5 : 5 ≤ n := by
    have hmod : n % 8 ≤ n := Nat.mod_le n 8
    simpa [h] using hmod
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 5) hn5
  have htag : 3 ≤ tag n := tag_ge_three_of_mod8_eq5 (n := n) h
  have hden : 8 ≤ 2 ^ (tag n) := by
    -- `2^3 ≤ 2^(tag n)`
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) htag)

  have h1 : shortcut n ≤ (3 * n + 1) / 8 := by
    -- bigger denominator => smaller quotient
    have := div_le_div_of_denom_le (a := 3 * n + 1) (d1 := 8) (d2 := 2 ^ (tag n)) hden (by decide : 0 < 8)
    simpa [Up2Gain.shortcut] using this

  have h2 : (3 * n + 1) / 8 < n := by
    -- use `3n+1 < 8n` for `n>0`
    have hle : 3 * n + 1 ≤ 4 * n := Up2Gain.local_bound n (show n ≥ 1 from Nat.succ_le_iff.2 hnpos)
    have hlt4 : 4 * n < 8 * n := Nat.mul_lt_mul_of_pos_right (by decide : 4 < 8) hnpos
    have hlt : 3 * n + 1 < n * 8 := by
      have : 3 * n + 1 < 8 * n := lt_of_le_of_lt hle hlt4
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).2 hlt

  exact lt_of_le_of_lt h1 h2

/-
## High-gain windows imply descent

This is the semantic “payoff” of the `Up2Gain` layer: a certificate `Window L n g m` with
`g ≥ 2*L+1` forces an actual numerical contraction, hence a strict decrease.
-/

theorem pow_v2_le (n : ℕ) (hn : 0 < n) : 2 ^ v2 n ≤ n := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [v2.eq_1]
  rw [if_neg hn0]
  by_cases hEven : n % 2 = 0
  · rw [if_pos hEven]
    have hdiv_lt : n / 2 < n := Nat.div_lt_self hn (by decide : 1 < 2)
    have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hEven
    have hle : 2 ≤ n := Nat.le_of_dvd hn h2dvd
    have hdiv_pos : 0 < n / 2 := Nat.div_pos hle (by decide : 0 < 2)
    have hIH : 2 ^ v2 (n / 2) ≤ n / 2 := ih (n / 2) hdiv_lt hdiv_pos
    have hmul : 2 * (2 ^ v2 (n / 2)) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hIH
    have hmul2 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have hle' : 2 * (2 ^ v2 (n / 2)) ≤ n := le_trans hmul hmul2
    have hpow : 2 ^ (1 + v2 (n / 2)) = 2 * (2 ^ v2 (n / 2)) := by
      calc
        2 ^ (1 + v2 (n / 2)) = 2 ^ (v2 (n / 2) + 1) := by simp [Nat.add_comm]
        _ = 2 ^ v2 (n / 2) * 2 ^ 1 := by simp [Nat.pow_add]
        _ = 2 ^ v2 (n / 2) * 2 := by simp
        _ = 2 * 2 ^ v2 (n / 2) := by simp [Nat.mul_comm]
    simpa [hpow] using hle'
  · rw [if_neg hEven]
    simpa using (Nat.succ_le_iff.2 hn)

theorem shortcut_pos (n : ℕ) : 0 < shortcut n := by
  have hnum_pos : 0 < 3 * n + 1 := Nat.succ_pos _
  have hden_pos : 0 < 2 ^ tag n := Nat.pow_pos (by decide : 0 < 2)
  have hden_le : 2 ^ tag n ≤ 3 * n + 1 := by
    simpa [tag] using (pow_v2_le (n := 3 * n + 1) hnum_pos)
  have : 0 < (3 * n + 1) / (2 ^ tag n) := Nat.div_pos hden_le hden_pos
  simpa [shortcut] using this

private theorem sumTagsAux_shift1 (L : ℕ) (tags : Fin (L + 1) → ℕ) (i acc : ℕ) :
    sumTagsAux (L + 1) tags (i + 1) acc =
      sumTagsAux L (fun j : Fin L => tags j.succ) i acc := by
  let tail : Fin L → ℕ := fun j => tags j.succ
  let p : ℕ → Prop := fun k =>
    ∀ i acc, (L - i = k) → sumTagsAux (L + 1) tags (i + 1) acc = sumTagsAux L tail i acc
  have hp : ∀ k, (∀ m, m < k → p m) → p k := by
    intro k ih i acc hk
    by_cases h : i < L
    · have hi1 : i + 1 < L + 1 := Nat.succ_lt_succ h
      rw [sumTagsAux.eq_1 (L := L + 1) (tags := tags) (i := i + 1) (acc := acc)]
      rw [dif_pos hi1]
      rw [sumTagsAux.eq_1 (L := L) (tags := tail) (i := i) (acc := acc)]
      rw [dif_pos h]
      simp only [tail]
      have hk' : L - (i + 1) < k := by
        have : L - (i + 1) < L - i := Nat.sub_lt_sub_left h (Nat.lt_succ_self i)
        simpa [hk] using this
      have pk' : p (L - (i + 1)) := ih (L - (i + 1)) hk'
      exact pk' (i + 1) (acc + tags ⟨i + 1, hi1⟩) rfl
    · have hi : ¬ i < L := h
      have hi1 : ¬ i + 1 < L + 1 := by
        intro hi1
        have : i < L := Nat.lt_of_succ_lt_succ hi1
        exact hi this
      rw [sumTagsAux.eq_1 (L := L + 1) (tags := tags) (i := i + 1) (acc := acc)]
      rw [dif_neg hi1]
      rw [sumTagsAux.eq_1 (L := L) (tags := tail) (i := i) (acc := acc)]
      rw [dif_neg hi]
  have pk : p (L - i) := Nat.strong_induction_on (L - i) hp
  exact pk i acc rfl

private theorem sumTagsAux_add_left (L : ℕ) (tags : Fin L → ℕ) (i acc add : ℕ) :
    sumTagsAux L tags i (acc + add) = acc + sumTagsAux L tags i add := by
  let p : ℕ → Prop := fun k =>
    ∀ i acc add, (L - i = k) → sumTagsAux L tags i (acc + add) = acc + sumTagsAux L tags i add
  have hp : ∀ k, (∀ m, m < k → p m) → p k := by
    intro k ih i acc add hk
    by_cases h : i < L
    · rw [sumTagsAux.eq_1 (L := L) (tags := tags) (i := i) (acc := acc + add)]
      rw [dif_pos h]
      rw [sumTagsAux.eq_1 (L := L) (tags := tags) (i := i) (acc := add)]
      rw [dif_pos h]
      have hk' : L - (i + 1) < k := by
        have : L - (i + 1) < L - i := Nat.sub_lt_sub_left h (Nat.lt_succ_self i)
        simpa [hk] using this
      have pk' : p (L - (i + 1)) := ih (L - (i + 1)) hk'
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        pk' (i + 1) acc (add + tags ⟨i, h⟩) rfl
    · have hi : ¬ i < L := h
      rw [sumTagsAux.eq_1 (L := L) (tags := tags) (i := i) (acc := acc + add)]
      rw [dif_neg hi]
      rw [sumTagsAux.eq_1 (L := L) (tags := tags) (i := i) (acc := add)]
      rw [dif_neg hi]
  have pk : p (L - i) := Nat.strong_induction_on (L - i) hp
  exact pk i acc add rfl

private theorem sumTags_succ (L : ℕ) (tags : Fin (L + 1) → ℕ) :
    sumTags tags = tags 0 + sumTags (fun i : Fin L => tags i.succ) := by
  cases L with
  | zero =>
      rw [sumTags.eq_1]
      rw [sumTagsAux.eq_1 (L := 1) (tags := tags) (i := 0) (acc := 0)]
      rw [dif_pos (Nat.succ_pos 0)]
      simp [sumTags, sumTagsAux]
  | succ L =>
      rw [sumTags.eq_1]
      rw [sumTagsAux.eq_1 (L := L + 2) (tags := tags) (i := 0) (acc := 0)]
      rw [dif_pos (Nat.succ_pos (L + 1))]
      -- normalize `0 + _` so the helper lemmas apply
      simp [Nat.zero_add] at *
      have hshift :
          sumTagsAux (L + 2) tags 1 (tags 0) =
            sumTagsAux (L + 1) (fun j : Fin (L + 1) => tags j.succ) 0 (tags 0) := by
        simpa using
          (sumTagsAux_shift1 (L := L + 1) (tags := tags) (i := 0) (acc := tags 0))
      have hadd :
          sumTagsAux (L + 1) (fun j : Fin (L + 1) => tags j.succ) 0 (tags 0) =
            tags 0 + sumTagsAux (L + 1) (fun j : Fin (L + 1) => tags j.succ) 0 0 := by
        simpa using
          (sumTagsAux_add_left (L := L + 1) (tags := fun j : Fin (L + 1) => tags j.succ)
            (i := 0) (acc := tags 0) (add := 0))
      calc
        sumTagsAux (L + 2) tags 1 (tags 0)
            = sumTagsAux (L + 1) (fun j : Fin (L + 1) => tags j.succ) 0 (tags 0) := hshift
        _ = tags 0 + sumTagsAux (L + 1) (fun j : Fin (L + 1) => tags j.succ) 0 0 := hadd
        _ = tags 0 + sumTags (fun i : Fin (L + 1) => tags i.succ) := by simp [sumTags]

private theorem shortcut_mul_pow_tag_le (n : ℕ) (hn : 1 ≤ n) :
    shortcut n * 2 ^ tag n ≤ 4 * n := by
  have h1 : shortcut n * 2 ^ tag n ≤ 3 * n + 1 := by
    -- `(a / b) * b ≤ a`
    simpa [shortcut] using Nat.div_mul_le_self (3 * n + 1) (2 ^ tag n)
  exact le_trans h1 (local_bound n hn)

private theorem window_bound_cert :
    ∀ {L : ℕ} (c : WindowCert L),
      IsValidWindow L c →
      1 ≤ c.states 0 →
        c.states (Fin.last L) * 2 ^ (sumTags c.tags) ≤ 4 ^ L * c.states 0 := by
  intro L c hValid hn0
  induction L with
  | zero =>
      -- `Fin.last 0 = 0`, `sumTags` over `Fin 0` is `0`.
      simp [sumTags, sumTagsAux]
  | succ L ih =>
      -- Peel off the first step, then apply IH to the tail certificate.
      let cTail : WindowCert L :=
        { states := fun i => c.states i.succ
          tags := fun i => c.tags i.succ }
      have hValidTail : IsValidWindow L cTail := by
        constructor
        · intro i
          have := hValid.1 (i := i.succ)
          simpa [cTail, Fin.castSucc_succ] using this
        · intro i
          have := hValid.2 (i := i.succ)
          simpa [cTail, Fin.castSucc_succ] using this

      have hn1 : 1 ≤ cTail.states 0 := by
        have hStep0 : c.states (1 : Fin (L + 2)) = shortcut (c.states 0) := by
          simpa using (hValid.2 (i := (0 : Fin (L + 1))))
        have hpos : 1 ≤ shortcut (c.states 0) := Nat.succ_le_iff.2 (shortcut_pos (c.states 0))
        have : 1 ≤ c.states (1 : Fin (L + 2)) := by simpa [hStep0] using hpos
        simpa [cTail] using this

      have hTail :
          cTail.states (Fin.last L) * 2 ^ (sumTags cTail.tags) ≤ 4 ^ L * cTail.states 0 :=
        ih (c := cTail) hValidTail hn1

      have hTag0 : c.tags (0 : Fin (L + 1)) = tag (c.states 0) := by
        simpa using (hValid.1 (i := (0 : Fin (L + 1))))
      have hStep0 : c.states (1 : Fin (L + 2)) = shortcut (c.states 0) := by
        simpa using (hValid.2 (i := (0 : Fin (L + 1))))

      have hStepIneq : c.states (1 : Fin (L + 2)) * 2 ^ (c.tags (0 : Fin (L + 1))) ≤
          4 * c.states 0 := by
        -- Rewrite the generic inequality `shortcut n * 2^tag n ≤ 4*n`.
        simpa [hStep0, hTag0] using shortcut_mul_pow_tag_le (n := c.states 0) hn0

      -- Multiply tail inequality by `2^(tag₀)`, then use the first-step bound.
      have hTail' :
          cTail.states (Fin.last L) * 2 ^ (sumTags cTail.tags) * 2 ^ (c.tags (0 : Fin (L + 1))) ≤
            (4 ^ L * cTail.states 0) * 2 ^ (c.tags (0 : Fin (L + 1))) := by
        exact Nat.mul_le_mul_right (2 ^ (c.tags (0 : Fin (L + 1)))) hTail

      have hSum :
          sumTags c.tags = c.tags (0 : Fin (L + 1)) + sumTags cTail.tags := by
        simpa [cTail] using (sumTags_succ (L := L) (tags := c.tags))

      have hPow :
          2 ^ (sumTags cTail.tags) * 2 ^ (c.tags (0 : Fin (L + 1))) = 2 ^ (sumTags c.tags) := by
        -- `2^(a) * 2^(b) = 2^(a+b)` and `sumTags` splits as `b + a`.
        calc
          2 ^ (sumTags cTail.tags) * 2 ^ (c.tags (0 : Fin (L + 1)))
              = 2 ^ (sumTags cTail.tags + c.tags (0 : Fin (L + 1))) := by
                  simp [Nat.pow_add, Nat.mul_assoc]
          _ = 2 ^ (c.tags (0 : Fin (L + 1)) + sumTags cTail.tags) := by
                simp [Nat.add_comm]
          _ = 2 ^ (sumTags c.tags) := by simpa [hSum]

      have hMain :
          cTail.states (Fin.last L) * 2 ^ (sumTags c.tags) ≤ 4 ^ (L + 1) * c.states 0 := by
        -- Use `hTail'`, rewrite the exponent, and bound `cTail.states 0 * 2^tag₀`.
        have hTail'' :
            cTail.states (Fin.last L) * 2 ^ (sumTags c.tags) ≤ (4 ^ L * cTail.states 0) * 2 ^ (c.tags (0 : Fin (L + 1))) := by
          -- reassociate and apply `hPow`
          simpa [Nat.mul_assoc, hPow] using hTail'

        have hRhs :
            (4 ^ L * cTail.states 0) * 2 ^ (c.tags (0 : Fin (L + 1))) ≤ 4 ^ (L + 1) * c.states 0 := by
          -- `4^L * (state₁ * 2^tag₀) ≤ 4^L * (4 * state₀) = 4^(L+1) * state₀`.
          have : 4 ^ L * (cTail.states 0 * 2 ^ (c.tags (0 : Fin (L + 1)))) ≤ 4 ^ L * (4 * c.states 0) :=
            Nat.mul_le_mul_left (4 ^ L) (by simpa [cTail, Nat.mul_assoc] using hStepIneq)
          -- normalize and rewrite `4^(L+1)`.
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.pow_succ] using this

        exact le_trans hTail'' hRhs

      -- Unfold `cTail.states (Fin.last L)` as `c.states (Fin.last (L+1))`.
      simpa [cTail, Fin.succ_last, Nat.mul_assoc] using hMain

private theorem window_mul_pow_le {L n g m : ℕ} (hn : 1 ≤ n) (hW : Window L n g m) :
    m * 2 ^ g ≤ 4 ^ L * n := by
  rcases hW with ⟨c, hValid, h0, hLast, hSum⟩
  have hIneq : c.states (Fin.last L) * 2 ^ (sumTags c.tags) ≤ 4 ^ L * c.states 0 :=
    window_bound_cert (c := c) hValid (by simpa [h0] using hn)
  simpa [h0, hLast, hSum] using hIneq

theorem window_highGain_mul_two_le {L n g m : ℕ} (hn : 1 ≤ n) (hW : Window L n g m)
    (hg : g ≥ 2 * L + 1) : m * 2 ≤ n := by
  have hBound : m * 2 ^ g ≤ 4 ^ L * n := window_mul_pow_le (L := L) (n := n) (g := g) (m := m) hn hW
  have hPowMon : 2 ^ (2 * L + 1) ≤ 2 ^ g :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hg
  have hPowEq : 2 ^ (2 * L + 1) = 2 * 4 ^ L := by
    calc
      2 ^ (2 * L + 1) = 2 ^ (2 * L) * 2 ^ 1 := by simp [Nat.pow_add]
      _ = 2 ^ (2 * L) * 2 := by simp
      _ = ((2 ^ 2) ^ L) * 2 := by simp [Nat.pow_mul]
      _ = 4 ^ L * 2 := by simp
      _ = 2 * 4 ^ L := by simp [Nat.mul_comm]
  have hDen : 2 * 4 ^ L ≤ 2 ^ g := by simpa [hPowEq] using hPowMon
  have hMul : m * (2 * 4 ^ L) ≤ 4 ^ L * n :=
    le_trans (Nat.mul_le_mul_left m hDen) hBound
  have hMul' : (m * 2) * 4 ^ L ≤ n * 4 ^ L := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMul
  have hPos : 0 < 4 ^ L := Nat.pow_pos (by decide : 0 < 4)
  exact Nat.le_of_mul_le_mul_right hMul' hPos

theorem window_highGain_implies_lt {L n g m : ℕ} (hn : 1 ≤ n) (hW : Window L n g m)
    (hg : g ≥ 2 * L + 1) : m < n := by
  have hm2 : m * 2 ≤ n := window_highGain_mul_two_le (L := L) (n := n) (g := g) (m := m) hn hW hg
  have hmle : m ≤ n := le_trans (Nat.le_mul_of_pos_right m (by decide : 0 < 2)) hm2
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hmne : m ≠ n := by
    intro hEq
    have hge : n ≥ n * 2 := by simpa [hEq] using hm2
    have hnlt : n < n * 2 := by
      simpa [Nat.mul_one, Nat.mul_assoc] using
        (Nat.mul_lt_mul_of_pos_left (by decide : 1 < 2) hnpos)
    exact (Nat.not_lt_of_ge hge) hnlt
  exact lt_of_le_of_ne hmle hmne

end RevHalt.Collatz
