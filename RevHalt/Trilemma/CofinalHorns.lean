import RevHalt.Trilemma.Trilemma
import RevHalt.Trilemma.Cycle

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

section

variable (Provable : Set PropT -> PropT -> Prop)
variable (K : RHKit)
variable (Machine : Code -> Trace)
variable (encode_halt : Code -> PropT)
variable (Cn : Set PropT -> Set PropT)
variable (A0 : ThState (PropT := PropT) Provable Cn)

-- ------------------------------------------------------------
-- 0) Generic helper: strict growth ⇒ f k ≥ k  (hence unbounded)
-- ------------------------------------------------------------

def StrictStep (f : Nat -> Nat) : Prop := ∀ k, f k < f (k+1)

lemma le_of_strictStep (f : Nat -> Nat) (h : StrictStep f) : ∀ k, k ≤ f k := by
  intro k
  induction k with
  | zero =>
      exact Nat.zero_le (f 0)
  | succ k ih =>
      have hk : f k < f (k+1) := h k
      -- from ih: k ≤ f k, and hk: f k + 1 ≤ f(k+1)
      have : k + 1 ≤ f k + 1 := Nat.succ_le_succ ih
      exact Nat.le_trans this (Nat.succ_le_of_lt hk)

lemma unbounded_of_strictStep (f : Nat -> Nat) (h : StrictStep f) :
    ∀ N, ∃ k, N ≤ f k := by
  intro N
  refine ⟨N, ?_⟩
  exact le_of_strictStep f h N

-- ------------------------------------------------------------
-- 1) Your cycleMode is periodic mod 3: exact evaluations
-- ------------------------------------------------------------

lemma cycleMode_three_mul (t : Nat) :
    cycleMode (3*t) = CycleMode.BC := by
  -- (3*t) % 3 = 0
  simp [cycleMode, Nat.mul_comm]

lemma cycleMode_three_mul_succ (t : Nat) :
    cycleMode (3*t + 1) = CycleMode.AC := by
  -- (3*t + 1) % 3 = 1
  simp [cycleMode, Nat.add_mod]

lemma cycleMode_three_mul_two (t : Nat) :
    cycleMode (3*t + 2) = CycleMode.AB := by
  -- (3*t + 2) % 3 = 2, so the match falls in the "_" case
  have hmod : (3*t + 2) % 3 = 2 := by
    -- simp can do this; if it fails in your environment, replace with a small arithmetic lemma
    simp [Nat.add_mod]
  -- rewrite the match using hmod
  simp [cycleMode, hmod]

-- ------------------------------------------------------------
-- 2) Cofinality of each mode (in k)
-- ------------------------------------------------------------

def CofinalK (P : Nat -> Prop) : Prop := ∀ K, ∃ k, K ≤ k ∧ P k

lemma cofinal_cycleMode_BC : CofinalK (fun k => cycleMode k = CycleMode.BC) := by
  intro K
  -- choose k = 3*K
  refine ⟨3*K, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_left K (by decide : 0 < 3)
  · simpa using cycleMode_three_mul (t := K)

lemma cofinal_cycleMode_AC : CofinalK (fun k => cycleMode k = CycleMode.AC) := by
  intro K
  -- choose k = 3*K + 1
  refine ⟨3*K + 1, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_mul_of_pos_left K (by decide : 0 < 3)) (Nat.le_add_right _ _)
  · simpa using cycleMode_three_mul_succ (t := K)

lemma cofinal_cycleMode_AB : CofinalK (fun k => cycleMode k = CycleMode.AB) := by
  intro K
  -- choose k = 3*K + 2
  refine ⟨3*K + 2, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_mul_of_pos_left K (by decide : 0 < 3)) (Nat.le_add_right _ _)
  · simpa using cycleMode_three_mul_two (t := K)

-- ------------------------------------------------------------
-- 3) Push cofinality from k to time indices n = cycleTimes k
--    and obtain each horn infinitely often along the subsequence.
-- ------------------------------------------------------------

-- Cofinality in N
def CofinalN (P : Nat -> Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ P n

-- “Horn predicates” as properties on times n.
def Horn_notAbsorbable_at
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (n : Nat) : Prop :=
  ∃ k,
    n = cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hIdem hProvCn witBC witAC witAB k
    ∧ cycleMode k = CycleMode.BC
    ∧ ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem (by
            -- hProvCn is in scope
            exact hProvCn) A0
          ((cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k) + 1)).Γ

def Horn_notOmegaAdmissible_at
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (n : Nat) : Prop :=
  ∃ k,
    n = cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hIdem hProvCn witBC witAC witAB k
    ∧ cycleMode k = CycleMode.AC
    ∧ ¬ OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem (by exact hProvCn) A0
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k)))

def Horn_notRouteIIAt
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (n : Nat) : Prop :=
  ∃ k,
    n = cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          hIdem hProvCn witBC witAC witAB k
    ∧ cycleMode k = CycleMode.AB
    ∧ ¬ RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem (by exact hProvCn) A0
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k)))

-- ------------------------------------------------------------
-- 4) Cofinality results: each horn appears cofinally often along n = cycleTimes k
-- ------------------------------------------------------------

theorem cofinal_horn_notAbsorbable
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n)) :
    CofinalN (Horn_notAbsorbable_at (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB) := by
  intro N
  -- pick a phase k with cycleMode k = BC and k large enough so cycleTimes k ≥ N
  have hStrict : StrictStep (fun k =>
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k) := by
    intro k
    -- your lemma cycleTimes_strictMono gives the strict step
    exact cycleTimes_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k

  -- choose k = 3*N (ensures mode BC) and also cycleTimes k ≥ k ≥ N
  let k : Nat := 3*N
  have hkMode : cycleMode k = CycleMode.BC := by
    simpa [k] using cycleMode_three_mul (t := N)
  have hkLeTime : k ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    exact le_of_strictStep _ hStrict k
  have hNleTime : N ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    have : N ≤ k := Nat.le_trans (Nat.le_mul_of_pos_left N (by decide : 0 < 3)) (Nat.le_refl _)
    exact Nat.le_trans this hkLeTime

  -- get the horn at phase k from strict_cycle_horns
  have hHornK :
      match cycleMode k with
      | .BC =>
          ¬ Absorbable Provable
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
              ((cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                hIdem hProvCn witBC witAC witAB k) + 1)).Γ
      | .AC =>
          True
      | .AB =>
          True := by
    have := strict_cycle_horns
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k
    cases hm : cycleMode k <;> simp [hm] at this ⊢
    · exact this

  -- now produce the cofinal witness n = cycleTimes k and the horn predicate
  refine ⟨
    cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k,
    hNleTime,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  simpa [hkMode] using hHornK

theorem cofinal_horn_notOmegaAdmissible
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n)) :
    CofinalN (Horn_notOmegaAdmissible_at (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB) := by
  intro N
  have hStrict : StrictStep (fun k =>
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k) := by
    intro k
    exact cycleTimes_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k

  -- Choose k = 3*N + 1 (mode AC)
  let k : Nat := 3*N + 1
  have hkMode : cycleMode k = CycleMode.AC := by
    simpa [k] using cycleMode_three_mul_succ (t := N)
  have hkLeTime : k ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    exact le_of_strictStep _ hStrict k
  have hNleTime : N ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    -- Proper inequality: N <= 3*N because N>=0 and 3>=1. Then 3*N <= 3*N+1.
    have hN_le_3N : N <= 3 * N := Nat.le_mul_of_pos_left N (by decide)
    exact Nat.le_trans (Nat.le_trans hN_le_3N (Nat.le_add_right _ 1)) hkLeTime

  have hHornK :
      match cycleMode k with
      | .AC =>
          ¬ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k)))
      | _ => True := by
    have := strict_cycle_horns
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k
    cases hm : cycleMode k <;> simp [hm] at this ⊢
    · exact this


  refine ⟨
    cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k,
    hNleTime,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  simpa [hkMode] using hHornK

theorem cofinal_horn_notRouteIIAt
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (P := fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (P := fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n)) :
    CofinalN (Horn_notRouteIIAt (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB) := by
  intro N
  have hStrict : StrictStep (fun k =>
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k) := by
    intro k
    exact cycleTimes_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k

  -- Choose k = 3*N + 2 (mode AB)
  let k : Nat := 3*N + 2
  have hkMode : cycleMode k = CycleMode.AB := by
    simpa [k] using cycleMode_three_mul_two (t := N)
  have hkLeTime : k ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    exact le_of_strictStep _ hStrict k
  have hNleTime : N ≤
      cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k := by
    have hN_le_3N : N <= 3 * N := Nat.le_mul_of_pos_left N (by decide)
    exact Nat.le_trans (Nat.le_trans hN_le_3N (Nat.le_add_right _ 2)) hkLeTime

  have hHornK :
      match cycleMode k with
      | .AB =>
          ¬ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k)))
      | _ => True := by
    have := strict_cycle_horns
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k
    cases hm : cycleMode k <;> simp [hm] at this ⊢
    · exact this

  refine ⟨
    cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      hIdem hProvCn witBC witAC witAB k,
    hNleTime,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  simpa [hkMode] using hHornK

end

end RevHalt.Trilemma
