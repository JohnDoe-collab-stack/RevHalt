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
-- 2) “Modes” and a visit policy sigma (periodic, but local)
--    You can swap sigma later for any other policy.
-- ============================================================

inductive Mode where
  | BC | AC | AB

def sigma (k : Nat) : Mode :=
  match k % 3 with
  | 0 => .BC
  | 1 => .AC
  | _ => .AB

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
      let N := prev + 1
      match sigma (k + 1) with
      | .BC => (witBC N).val
      | .AC => (witAC N).val
      | .AB => (witAB N).val

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
        (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k) := by
  induction k with
  | zero =>
      simp [times, sigma]
      -- sigma 0 = BC (since 0%3=0), so this is witBC 0
      exact (witBC 0).property.2
  | succ k ih =>
      simp [times]
      -- reduce to witness at N = prev+1, picking the mode sigma (k+1)
      set prev :=
        times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k with hPrev
      set N := prev + 1 with hN
      cases hm : sigma (k + 1) <;> simp [Pair]
      · exact (witBC N).property.2
      · exact (witAC N).property.2
      · exact (witAB N).property.2

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
        (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k
      <
    times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB (k + 1) := by
  simp [times]
  set prev :=
    times (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k with hPrev
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
-- 5) The horn forcing along the subsequence (replaces strict_cycle_horns)
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
                hIdem hProvCn witBC witAC witAB k) + 1)).Γ
    | .AC =>
        ¬ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (times (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k)))
    | .AB =>
        ¬ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (times (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k))) := by
  have hPair :=
    times_spec (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k
  cases hk : sigma k <;> simp [Pair, hk] at hPair ⊢
  · -- BC: have B ∧ C at time, deduce ¬A at successor via trilemma lemma
    rcases hPair with ⟨hB, hC⟩
    exact omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hB hC
  · -- AC: have A ∧ C at time, deduce ¬B
    rcases hPair with ⟨hA, hC⟩
    exact absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hA hC
  · -- AB: have A ∧ B at time, deduce ¬C
    rcases hPair with ⟨hA, hB⟩
    exact absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (times (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hA hB

end

end RevHalt.Trilemma
