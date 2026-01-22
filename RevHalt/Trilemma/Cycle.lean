import RevHalt.Trilemma.Trilemma

namespace RevHalt.Trilemma

universe u

variable {PropT : Type u}
variable {Code : Type u}

section

variable (Provable : Set PropT -> PropT -> Prop)
variable (K : RHKit)
variable (Machine : Code -> Trace)
variable (encode_halt : Code -> PropT)
variable (Cn : Set PropT -> Set PropT)
variable (A0 : ThState (PropT := PropT) Provable Cn)

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

def Cofinal (P : Nat -> Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P n

inductive CycleMode where
  | BC
  | AC
  | AB

def cycleMode (k : Nat) : CycleMode :=
  match k % 3 with
  | 0 => .BC
  | 1 => .AC
  | _ => .AB

def Pair (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn) :
    CycleMode -> Nat -> Prop
  | .BC, n => B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n
              ∧
              C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n
  | .AC, n => A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n
              ∧
              C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n
  | .AB, n => A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n
              ∧
              B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
                (Cn := Cn) (A0 := A0) hIdem hProvCn n

/-- Witness function type for cofinal property: given any N, provides an n ≥ N satisfying P -/
def CofinalWitness (P : Nat → Prop) : Type :=
  (N : Nat) → { n : Nat // N ≤ n ∧ P n }

/-- From a CofinalWitness we can derive the Cofinal property -/
theorem cofinal_of_witness {P : Nat → Prop} (w : CofinalWitness P) : Cofinal P :=
  fun N => ⟨(w N).val, (w N).property⟩

theorem exists_pair_from_cofinal
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (hBC : Cofinal (fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (hAC : Cofinal (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (hAB : Cofinal (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (m : CycleMode) (N : Nat) :
    ∃ n, N ≤ n ∧ Pair (Provable := Provable) (K := K) (Machine := Machine)
      (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn m n := by
  cases m with
  | BC =>
      simpa [Pair] using hBC N
  | AC =>
      simpa [Pair] using hAC N
  | AB =>
      simpa [Pair] using hAB N

/-- Computable cycle times using explicit witness functions for each pair type -/
def cycleTimes
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n)) :
    Nat → Nat
  | 0 =>
      match cycleMode 0 with
      | .BC => (witBC 0).val
      | .AC => (witAC 0).val
      | .AB => (witAB 0).val
  | k + 1 =>
      let prev := cycleTimes hIdem hProvCn witBC witAC witAB k
      let N := prev + 1
      match cycleMode (k + 1) with
      | .BC => (witBC N).val
      | .AC => (witAC N).val
      | .AB => (witAB N).val

theorem cycleTimes_spec
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (k : Nat) :
    Pair (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) hIdem hProvCn (cycleMode k)
      (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k) := by
  induction k with
  | zero =>
      simp only [cycleTimes, cycleMode]
      exact (witBC 0).property.2
  | succ k _ih =>
      simp only [cycleTimes]
      set prev := cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k with hPrev
      set N := prev + 1 with hN
      match hm : cycleMode (k + 1) with
      | .BC =>
          simp only [Pair]
          exact (witBC N).property.2
      | .AC =>
          simp only [Pair]
          exact (witAC N).property.2
      | .AB =>
          simp only [Pair]
          exact (witAB N).property.2

theorem cycleTimes_strictMono
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (k : Nat) :
    cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k
      <
    cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB (k + 1) := by
  simp only [cycleTimes]
  set prev := cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
    hIdem hProvCn witBC witAC witAB k with hPrev
  set N := prev + 1 with hN
  have hBound : N ≤ match cycleMode (k + 1) with
    | .BC => (witBC N).val
    | .AC => (witAC N).val
    | .AB => (witAB N).val := by
    match hm : cycleMode (k + 1) with
    | .BC => exact (witBC N).property.1
    | .AC => exact (witAC N).property.1
    | .AB => exact (witAB N).property.1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self prev) hBound

theorem strict_cycle_horns
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (witBC : CofinalWitness (fun n =>
      B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAC : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (witAB : CofinalWitness (fun n =>
      A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
        (Cn := Cn) (A0 := A0) hIdem hProvCn n
      ∧ B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn n))
    (k : Nat) :
    match cycleMode k with
    | .BC =>
        ¬ Absorbable Provable
            (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
              ((cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                hIdem hProvCn witBC witAC witAB k) + 1)).Γ
    | .AC =>
        ¬ OmegaAdmissible Provable Cn
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k)))
    | .AB =>
        ¬ RouteIIAt Provable K Machine encode_halt
            (omegaΓ Provable K Machine encode_halt Cn hIdem hProvCn
              (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0
                (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
                  (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
                  hIdem hProvCn witBC witAC witAB k))) := by
  have hPair := cycleTimes_spec (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn witBC witAC witAB k
  cases hk : cycleMode k with
  | BC =>
    have hPair' :
        B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k)
          ∧
        C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k) := by
      simpa [Pair, hk] using hPair
    rcases hPair' with ⟨hB, hC⟩
    exact omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hB hC
  | AC =>
    have hPair' :
        A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k)
          ∧
        C (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k) := by
      simpa [Pair, hk] using hPair
    rcases hPair' with ⟨hA, hC⟩
    exact absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hA hC
  | AB =>
    have hPair' :
        A (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k)
          ∧
        B (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
            (Cn := Cn) (A0 := A0) hIdem hProvCn
            (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              hIdem hProvCn witBC witAC witAB k) := by
      simpa [Pair, hk] using hPair
    rcases hPair' with ⟨hA, hB⟩
    exact absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0)
      hMono hCnExt hIdem hProvCn
      (cycleTimes (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        hIdem hProvCn witBC witAC witAB k)
      hA hB

end

end RevHalt.Trilemma
