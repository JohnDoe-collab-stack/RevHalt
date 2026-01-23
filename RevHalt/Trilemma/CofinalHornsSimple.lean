import RevHalt.Trilemma.Trilemma

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

-- ============================================================
-- 1) Predicates A,B,C (same as your Cycle.lean)
-- ============================================================

def A (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn) (n : Nat) : Prop :=
  Absorbable Provable
    (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 (n + 1)).Γ

def B (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn) (n : Nat) : Prop :=
  OmegaAdmissible Provable Cn
    (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n))

def C (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn) (n : Nat) : Prop :=
  RouteIIAt Provable K Machine encode_halt
    (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
      (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n))

-- ============================================================
-- 2) “Modes” and a visit policy sigma (arbitrary parameter)
-- ============================================================

inductive Mode where
  | BC | AC | AB

variable (sigma : Nat -> Mode)

-- ============================================================
-- 3) Pair predicates (same as Cycle.lean but with Mode)
-- ============================================================

def Pair (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn) :
    Mode -> Nat -> Prop
  | .BC, n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
  | .AC, n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
  | .AB, n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n

-- ============================================================
-- 4) Cofinal witnesses and subsequence times (no Cycle import)
-- ============================================================

/-- Witness function type for cofinal property: for any N, produce n ≥ N with P n. -/
def CofinalWitness (P : Nat → Prop) : Type :=
  (N : Nat) → { n : Nat // N ≤ n ∧ P n }

/-- Subsequence times driven by witnesses; strictly increasing by construction. -/
def times
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB)) :
    Nat → Nat
  | 0 =>
      match sigma 0 with
      | .BC => (witBC 0).val
      | .AC => (witAC 0).val
      | .AB => (witAB 0).val
  | k + 1 =>
      let prev := times hIdem hProvCn witBC witAC witAB k
      let next_N := prev + 1
      match sigma (k + 1) with
      | .BC => (witBC next_N).val
      | .AC => (witAC next_N).val
      | .AB => (witAB next_N).val

theorem times_spec
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (k : Nat) :
    Pair (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) hIdem hProvCn (sigma k)
      (times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB k) := by
  induction k with
  | zero =>
      simp [times]
      -- sigma 0 = BC (since 0%3=0), so this is witBC 0
      exact match sigma 0 with
      | .BC => (witBC 0).property.2
      | .AC => (witAC 0).property.2
      | .AB => (witAB 0).property.2
  | succ k ih =>
      simp [times]
      -- reduce to witness at N = prev+1, picking the mode sigma (k+1)
      set prev :=
        times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB k with hPrev
      set next_N := prev + 1 with hN
      cases hm : sigma (k + 1) <;> simp [Pair]
      · exact (witBC next_N).property.2
      · exact (witAC next_N).property.2
      · exact (witAB next_N).property.2

theorem times_strictMono
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (k : Nat) :
    times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB k
      <
    times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB (k + 1) := by
  simp [times]
  set prev :=
    times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB k with hPrev
  set N := prev + 1 with hN
  have hBound : N ≤ match sigma (k + 1) with
    | .BC => (witBC N).val
    | .AC => (witAC N).val
    | .AB => (witAB N).val := by
    cases hm : sigma (k + 1) <;> simp []
    · exact (witBC N).property.1
    · exact (witAC N).property.1
    · exact (witAB N).property.1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self prev) hBound

-- ============================================================
-- 5) The horn forcing along the subsequence
-- ============================================================

theorem strict_subseq_horns
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (k : Nat) :
    match sigma k with
    | .BC =>
        ¬ Absorbable Provable
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
              ((times (Provable := Provable) (K := K) (Machine := Machine)
                (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                sigma hIdem hProvCn witBC witAC witAB k) + 1)).Γ
    | .AC =>
        ¬ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (times (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  sigma hIdem hProvCn witBC witAC witAB k)))
    | .AB =>
        ¬ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (times (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  sigma hIdem hProvCn witBC witAC witAB k))) := by
  have hPair :=
    times_spec (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) sigma hIdem hProvCn witBC witAC witAB k
  cases hk : sigma k <;> simp [Pair, hk] at hPair ⊢
  · -- BC: have B ∧ C at time, deduce ¬A at successor via trilemma lemma
    rcases hPair with ⟨hB, hC⟩
    exact omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k)
      hB hC
  · -- AC: have A ∧ C at time, deduce ¬B
    rcases hPair with ⟨hA, hC⟩
    exact absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k)
      hA hC
  · -- AB: have A ∧ B at time, deduce ¬C
    rcases hPair with ⟨hA, hB⟩
    exact absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k)
      hA hB

-- ============================================================
-- 6) Cofinality transfer from sigma to horns
-- ============================================================

def CofinalK (P : Nat → Prop) : Prop :=
  ∀ K0, ∃ k, K0 ≤ k ∧ P k

def SigmaCofinal (m : Mode) : Prop :=
  CofinalK (fun k => sigma k = m)

def CofinalN (P : Nat → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P n

def StrictStep (f : Nat → Nat) : Prop := ∀ k, f k < f (k+1)

lemma le_of_strictStep (f : Nat → Nat) (h : StrictStep f) : ∀ k, k ≤ f k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le (f 0)
  | succ k ih =>
      have hk : f k < f (k+1) := h k
      have : k+1 ≤ f k + 1 := Nat.succ_le_succ ih
      exact Nat.le_trans this (Nat.succ_le_of_lt hk)

-- ============================================================
-- Clone #0: BC branch (¬Absorbable appears cofinally often)
-- ============================================================

def HornBC_at_time
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (n : Nat) : Prop :=
  ∃ k,
    n = times (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          sigma hIdem hProvCn witBC witAC witAB k
    ∧ sigma k = Mode.BC
    ∧ ¬ Absorbable Provable
        (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
          ((times (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              sigma hIdem hProvCn witBC witAC witAB k) + 1)).Γ

theorem cofinal_hornBC_along_times
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (hBC : SigmaCofinal sigma .BC) :
    CofinalN (HornBC_at_time (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB) := by
  intro N
  -- pick k >= N with sigma k = BC
  rcases hBC N with ⟨k, hkN, hkMode⟩

  -- times is strictly increasing, so k ≤ times k, hence N ≤ times k
  have hStrict : StrictStep (fun t =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB t) := by
    intro t
    exact times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB t

  have hk_le_timesk : k ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    le_of_strictStep _ hStrict k

  have hN_le_timesk : N ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    Nat.le_trans hkN hk_le_timesk

  -- horn forced at phase k
  have hHornK :=
    strict_subseq_horns (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k

  refine ⟨
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB k,
    hN_le_timesk,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  -- extract BC branch from match
  simpa [hkMode] using hHornK


-- ============================================================
-- Clone #1: AC branch (¬OmegaAdmissible appears cofinally often)
-- ============================================================

def HornAC_at_time
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (n : Nat) : Prop :=
  ∃ k,
    n = times (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          sigma hIdem hProvCn witBC witAC witAB k
    ∧ sigma k = Mode.AC
    ∧ ¬ OmegaAdmissible Provable Cn
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
            (times (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              sigma hIdem hProvCn witBC witAC witAB k)))

theorem cofinal_hornAC_along_times
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (hAC : SigmaCofinal sigma .AC) :
    CofinalN (HornAC_at_time (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB) := by
  intro N
  rcases hAC N with ⟨k, hkN, hkMode⟩

  have hStrict : StrictStep (fun t =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB t) := by
    intro t
    exact times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB t

  have hk_le_timesk : k ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    le_of_strictStep _ hStrict k

  have hN_le_timesk : N ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    Nat.le_trans hkN hk_le_timesk

  have hHornK :=
    strict_subseq_horns (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k

  refine ⟨
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB k,
    hN_le_timesk,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  simpa [hkMode] using hHornK


-- ============================================================
-- Clone #2: AB branch (¬RouteIIAt appears cofinally often)
-- ============================================================

def HornAB_at_time
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (n : Nat) : Prop :=
  ∃ k,
    n = times (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          sigma hIdem hProvCn witBC witAC witAB k
    ∧ sigma k = Mode.AB
    ∧ ¬ RouteIIAt Provable K Machine encode_halt
        (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
          (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
            (times (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              sigma hIdem hProvCn witBC witAC witAB k)))

theorem cofinal_hornAB_along_times
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn .AB))
    (hAB : SigmaCofinal sigma .AB) :
    CofinalN (HornAB_at_time (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB) := by
  intro N
  rcases hAB N with ⟨k, hkN, hkMode⟩

  have hStrict : StrictStep (fun t =>
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB t) := by
    intro t
    exact times_strictMono (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB t

  have hk_le_timesk : k ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    le_of_strictStep _ hStrict k

  have hN_le_timesk : N ≤
      times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        sigma hIdem hProvCn witBC witAC witAB k :=
    Nat.le_trans hkN hk_le_timesk

  have hHornK :=
    strict_subseq_horns (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma
      (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
      (witBC := witBC) (witAC := witAC) (witAB := witAB) k

  refine ⟨
    times (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
      sigma hIdem hProvCn witBC witAC witAB k,
    hN_le_timesk,
    ?_⟩
  refine ⟨k, rfl, hkMode, ?_⟩
  simpa [hkMode] using hHornK

end

end RevHalt.Trilemma
