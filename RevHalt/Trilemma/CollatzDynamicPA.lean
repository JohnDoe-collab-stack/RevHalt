/-
  CollatzDynamicPA.lean

  But :
  - Mettre Collatz DANS le même fichier, et l’interfacer avec :
      * RevHalt.Trilemma.CofinalHornsSimple
      * RevHalt.Trilemma.CofinalHornsPA  (branche Strong : PairPA, cofinalités PA sur visites)
  - σ : Nat → Mode est défini de façon déterministe à partir d’un seed.

  Contrainte demandée :
  - pas de Classical
  - pas de noncomputable
  - éviter les “trucs” type mod6 : on utilise une classification par "branche else"
    (test x = 1, puis parité), donc 3 cas sans mod6.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

namespace Collatz

/-- Étape Collatz (sur Nat). -/
def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Itération Collatz : `iter k seed` = état après k pas. -/
def iter : Nat → Nat → Nat
  | 0,     seed => seed
  | k + 1, seed => iter k (step seed)

/-
  Encodage σ : Nat → Mode à partir de la trajectoire Collatz.

  Classification (sans mod6) :
    - si x = 1      => BC
    - sinon si x pair => AC
    - sinon           => AB
-/
def sigmaOf (seed : Nat) : Nat → Mode :=
  fun k =>
    let x := iter k seed
    if x = 1 then Mode.BC
    else if x % 2 = 0 then Mode.AC
    else Mode.AB

end Collatz

namespace Collatz

/-- Composition d’itérations : `iter (a+b) seed = iter b (iter a seed)`. -/
lemma iter_add (a b seed : Nat) : iter (a + b) seed = iter b (iter a seed) := by
  induction a generalizing seed with
  | zero =>
      simp [iter]
  | succ a ih =>
      -- (succ a) + b = succ (a + b) et iter (succ n) seed = iter n (step seed)
      simp [Nat.succ_add, iter, ih]

/-- Calcul explicite : `iter 3 1 = 1` (cycle 1→4→2→1). -/
lemma iter_three_one : iter 3 1 = 1 := by
  simp [iter, step]

/-- Période 3 à partir de 1 : `iter (d+3) 1 = iter d 1`. -/
lemma iter_period3_one (d : Nat) : iter (d + 3) 1 = iter d 1 := by
  have h3 : iter 3 1 = 1 := iter_three_one
  calc
    iter (d + 3) 1 = iter (3 + d) 1 := by
      simp [Nat.add_comm]
    _ = iter d (iter 3 1) := by
      simpa using (iter_add (a := 3) (b := d) (seed := 1))
    _ = iter d 1 := by
      simp [h3]

/-- Si `iter T seed = 1`, alors `iter (T+d) seed = iter d 1`. -/
lemma iter_after_hits_one {seed T d : Nat} (h : iter T seed = 1) :
    iter (T + d) seed = iter d 1 := by
  calc
    iter (T + d) seed = iter d (iter T seed) := by
      simpa using (iter_add (a := T) (b := d) (seed := seed))
    _ = iter d 1 := by
      simp [h]

/-- Stabilité de `sigmaOf` par +3 une fois 1 atteint. -/
lemma sigmaOf_add3_after_hits_one {seed T d : Nat} (h : iter T seed = 1) :
    sigmaOf seed (T + (d + 3)) = sigmaOf seed (T + d) := by
  have hiter :
      iter (T + (d + 3)) seed = iter (T + d) seed := by
    calc
      iter (T + (d + 3)) seed = iter (d + 3) 1 := by
        simpa [Nat.add_assoc] using (iter_after_hits_one (seed := seed) (T := T) (d := d + 3) h)
      _ = iter d 1 := by
        simpa using (iter_period3_one d)
      _ = iter (T + d) seed := by
        simpa using (iter_after_hits_one (seed := seed) (T := T) (d := d) h).symm
  simp [sigmaOf, hiter]

/--
Une fois `1` atteint au temps `T`, `sigmaOf seed (T+d)` vaut `BC` ou `AC` pour tout `d`.
-/
theorem sigmaOf_after_hits_one_add (seed T : Nat) (h : iter T seed = 1) :
    ∀ d, sigmaOf seed (T + d) = Mode.BC ∨ sigmaOf seed (T + d) = Mode.AC := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih
  cases d with
  | zero =>
      left
      simp [sigmaOf, h]
  | succ d1 =>
      cases d1 with
      | zero =>
          right
          have hiter : iter (T + 1) seed = 4 := by
            calc
              iter (T + 1) seed = iter 1 (iter T seed) := by
                simpa using (iter_add (a := T) (b := 1) (seed := seed))
              _ = iter 1 1 := by simp [h]
              _ = 4 := by simp [iter, step]
          simp [sigmaOf, hiter]
      | succ d2 =>
          cases d2 with
          | zero =>
              right
              have hiter : iter (T + 2) seed = 2 := by
                calc
                  iter (T + 2) seed = iter 2 (iter T seed) := by
                    simpa using (iter_add (a := T) (b := 2) (seed := seed))
                  _ = iter 2 1 := by simp [h]
                  _ = 2 := by simp [iter, step]
              simp [sigmaOf, hiter]
          | succ d3 =>
              -- d = d3 + 3
              have hd3lt :
                  d3 < Nat.succ (Nat.succ (Nat.succ d3)) := by
                have h1 : d3 < Nat.succ d3 := Nat.lt_succ_self d3
                have h2 : Nat.succ d3 < Nat.succ (Nat.succ d3) := Nat.lt_succ_self (Nat.succ d3)
                have h3 : Nat.succ (Nat.succ d3) < Nat.succ (Nat.succ (Nat.succ d3)) :=
                  Nat.lt_succ_self (Nat.succ (Nat.succ d3))
                exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

              have ihd :
                  sigmaOf seed (T + d3) = Mode.BC ∨ sigmaOf seed (T + d3) = Mode.AC :=
                ih d3 hd3lt

              have hs0 :
                  sigmaOf seed (T + (d3 + 3)) = sigmaOf seed (T + d3) :=
                sigmaOf_add3_after_hits_one (seed := seed) (T := T) (d := d3) h

              have hs :
                  sigmaOf seed (T + Nat.succ (Nat.succ (Nat.succ d3))) = sigmaOf seed (T + d3) := by
                simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hs0

              cases ihd with
              | inl hBC =>
                  exact Or.inl (hs.trans hBC)
              | inr hAC =>
                  exact Or.inr (hs.trans hAC)

/--
Forme “à partir de k ≥ T” : si `iter T seed = 1`, alors pour tout `k ≥ T`,
`sigmaOf seed k` vaut `BC` ou `AC`.
-/
theorem sigmaOf_after_hits_one_ge (seed T : Nat) (h : iter T seed = 1) :
    ∀ k, T ≤ k → sigmaOf seed k = Mode.BC ∨ sigmaOf seed k = Mode.AC := by
  intro k hk
  rcases Nat.exists_eq_add_of_le hk with ⟨d, rfl⟩
  simpa [Nat.add_assoc] using sigmaOf_after_hits_one_add (seed := seed) (T := T) h d

end Collatz

namespace Collatz

/-- Propriété “positive” : à partir d’un rang, on ne voit plus que BC ou AC. -/
def EventuallyBCorAC (seed : Nat) : Prop :=
  ∃ N, ∀ k, N ≤ k → sigmaOf seed k = Mode.BC ∨ sigmaOf seed k = Mode.AC

/-- Arrivée à 1 ⇒ à partir de T, seulement BC ou AC (donc AB s’éteint “positivement”). -/
theorem eventuallyBCorAC_of_hits_one (seed T : Nat) (h : iter T seed = 1) :
    EventuallyBCorAC seed := by
  refine ⟨T, ?_⟩
  intro k hk
  -- on réécrit k = T + d
  rcases Nat.exists_eq_add_of_le hk with ⟨d, rfl⟩
  -- et on applique ton lemme de stabilité
  simpa [Nat.add_assoc] using (sigmaOf_after_hits_one_add (seed := seed) (T := T) h d)

/-- Calcul : à l’instant T+1 on est sur 4, donc sigma = AC. -/
lemma sigmaOf_T_add_one_eq_AC (seed T : Nat) (h : iter T seed = 1) :
    sigmaOf seed (T + 1) = Mode.AC := by
  have hiter : iter (T + 1) seed = 4 := by
    calc
      iter (T + 1) seed = iter 1 (iter T seed) := by
        simpa using (iter_add (a := T) (b := 1) (seed := seed))
      _ = iter 1 1 := by simp [h]
      _ = 4 := by simp [iter, step]
  simp [sigmaOf, hiter]

/-- Calcul : à l’instant T+2 on est sur 2, donc sigma = AC. -/
lemma sigmaOf_T_add_two_eq_AC (seed T : Nat) (h : iter T seed = 1) :
    sigmaOf seed (T + 2) = Mode.AC := by
  have hiter : iter (T + 2) seed = 2 := by
    calc
      iter (T + 2) seed = iter 2 (iter T seed) := by
        simpa using (iter_add (a := T) (b := 2) (seed := seed))
      _ = iter 2 1 := by simp [h]
      _ = 2 := by simp [iter, step]
  simp [sigmaOf, hiter]

/-- Arrivée à 1 ⇒ sigma(T + 3n) = BC pour tout n. -/
lemma sigmaOf_T_add_three_mul_eq_BC (seed T n : Nat) (h : iter T seed = 1) :
    sigmaOf seed (T + 3 * n) = Mode.BC := by
  induction n with
  | zero =>
      simp [sigmaOf, h]
  | succ n ih =>
      have hs :=
        sigmaOf_add3_after_hits_one (seed := seed) (T := T) (d := 3 * n) h
      calc
        sigmaOf seed (T + 3 * (n + 1))
            = sigmaOf seed (T + ((3 * n) + 3)) := by
                simp [Nat.mul_succ]
        _ = sigmaOf seed (T + 3 * n) := by
                simpa [Nat.add_assoc] using hs
        _ = Mode.BC := ih

/-- Arrivée à 1 ⇒ sigma(T + (3n+1)) = AC pour tout n. -/
lemma sigmaOf_T_add_three_mul_add1_eq_AC (seed T n : Nat) (h : iter T seed = 1) :
    sigmaOf seed (T + (3 * n + 1)) = Mode.AC := by
  induction n with
  | zero =>
      simpa [Nat.mul_zero, Nat.zero_add, Nat.add_assoc] using
        (sigmaOf_T_add_one_eq_AC (seed := seed) (T := T) h)
  | succ n ih =>
      have hs :=
        sigmaOf_add3_after_hits_one (seed := seed) (T := T) (d := (3 * n + 1)) h
      have hrew : 3 * (n + 1) + 1 = (3 * n + 1) + 3 := by
        simp [Nat.mul_succ,Nat.add_left_comm, Nat.add_comm]
      calc
        sigmaOf seed (T + (3 * (n + 1) + 1))
            = sigmaOf seed (T + ((3 * n + 1) + 3)) := by
                simp [hrew, Nat.add_assoc]
        _ = sigmaOf seed (T + (3 * n + 1)) := by
                simpa [Nat.add_assoc] using hs
        _ = Mode.AC := ih

/-- Arrivée à 1 ⇒ sigma(T + (3n+2)) = AC pour tout n. -/
lemma sigmaOf_T_add_three_mul_add2_eq_AC (seed T n : Nat) (h : iter T seed = 1) :
    sigmaOf seed (T + (3 * n + 2)) = Mode.AC := by
  induction n with
  | zero =>
      simpa [Nat.mul_zero, Nat.zero_add, Nat.add_assoc] using
        (sigmaOf_T_add_two_eq_AC (seed := seed) (T := T) h)
  | succ n ih =>
      have hs :=
        sigmaOf_add3_after_hits_one (seed := seed) (T := T) (d := (3 * n + 2)) h
      have hrew : 3 * (n + 1) + 2 = (3 * n + 2) + 3 := by
        simp [Nat.mul_succ,Nat.add_left_comm, Nat.add_comm]
      calc
        sigmaOf seed (T + (3 * (n + 1) + 2))
            = sigmaOf seed (T + ((3 * n + 2) + 3)) := by
                simp [hrew, Nat.add_assoc]
        _ = sigmaOf seed (T + (3 * n + 2)) := by
                simpa [Nat.add_assoc] using hs
        _ = Mode.AC := ih

/-- Arrivée à 1 ⇒ BC est cofinal (au sens SigmaCofinal) pour sigmaOf. -/
theorem sigmaOf_SigmaCofinal_BC_of_hits_one (seed T : Nat) (h : iter T seed = 1) :
    SigmaCofinal (sigmaOf seed) Mode.BC := by
  intro N0
  refine ⟨T + 3 * N0, ?_, ?_⟩
  · have hN0 : N0 ≤ 3 * N0 := Nat.le_mul_of_pos_left N0 (by decide : 0 < 3)
    exact Nat.le_trans hN0 (Nat.le_add_left _ _)
  · simpa [Nat.add_assoc] using
      (sigmaOf_T_add_three_mul_eq_BC (seed := seed) (T := T) (n := N0) h)

/-- Arrivée à 1 ⇒ AC est cofinal (au sens SigmaCofinal) pour sigmaOf. -/
theorem sigmaOf_SigmaCofinal_AC_of_hits_one (seed T : Nat) (h : iter T seed = 1) :
    SigmaCofinal (sigmaOf seed) Mode.AC := by
  intro N0
  refine ⟨T + (3 * N0 + 1), ?_, ?_⟩
  · have hN0 : N0 ≤ 3 * N0 := Nat.le_mul_of_pos_left N0 (by decide : 0 < 3)
    have hN0' : N0 ≤ 3 * N0 + 1 := Nat.le_trans hN0 (Nat.le_succ _)
    exact Nat.le_trans hN0' (Nat.le_add_left _ _)
  · simpa [Nat.add_assoc] using
      (sigmaOf_T_add_three_mul_add1_eq_AC (seed := seed) (T := T) (n := N0) h)

end Collatz


/-
  Instance "Collatz + DynamicPA Strong" :
  On fixe seed, donc on fixe σ := sigmaOf seed.
  Puis on applique directement le théorème Strong final déjà prouvé dans CofinalHornsPA.
-/
section CollatzDynamicPA

-- Contexte RevHalt / Trilemma
variable {Provable : Set PropT -> PropT -> Prop}
variable {K : RHKit}
variable {Machine : Code -> Trace}
variable {encode_halt : Code → PropT}
variable {Cn : Set PropT → Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

-- Hypothèses structurelles (celles utilisées partout dans le cadre)
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

-- Seed Collatz, et σ dérivé
variable (seed : Nat)
abbrev σ : Nat → Mode := Collatz.sigmaOf seed

-- Axiomes "PA internes" (comme ensemble de PropT)
variable (PAax : Set PropT)

/-
  Théorème : Collatz instancie σ, et sous :
    - cofinalité de σ sur chaque Mode,
    - witnesses forts PairPA pour chaque Mode,
  on obtient :
    - cofinalité des trois cornes,
    - cofinalité de PA sur les visites BC/AC/AB.
-/
theorem collatz_dynamicPA_Strong
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBC : SigmaCofinal (σ seed) .BC)
    (hAC : SigmaCofinal (σ seed) .AC)
    (hAB : SigmaCofinal (σ seed) .AB)
    (witBC :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC))
    (witAC :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC))
    (witAB :
      CofinalWitness
        (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
          (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB)) :
    let wBC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC witBC
    let wAC :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC witAC
    let wAB :=
      toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
        (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 (σ seed) hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := (σ seed)) hIdem hProvCn PAax .AB witBC witAC witAB) := by
  -- Application directe du théorème Strong final déjà prouvé
  exact dynamic_trilemma_with_PA_Strong_final
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
    (Cn := Cn) (A0 := A0) (sigma := (σ seed)) (hIdem := hIdem) (hProvCn := hProvCn)
    PAax hMono hCnExt hBC hAC hAB witBC witAC witAB

end CollatzDynamicPA

end RevHalt.Trilemma
