/-
  CollatzDynamicPA.lean

  Fichier unique :
  - Collatz (step/iter)
  - Construction d’un \sigma : Nat → Mode déterministe à partir d’un seed,
    avec un cadencement (mod 6) garantissant BC/AC/AB cofinalement.
  - Preuves SigmaCofinal pour ce \sigma (dans ce fichier)
  - Instanciation directe du théorème Strong final (CofinalHornsPA)

  Principe :
  - Aux phases k ≡ 0,1,2 (mod 6), \sigma force respectivement BC, AC, AB.
  - Aux phases k ≡ 3,4,5 (mod 6), \sigma lit Collatz (seed) via (iter k seed) mod 3.

  Ainsi, la partie Collatz reste exploitable (traces locales), et la cofinalité
  des trois modes est prouvable par arithmétique élémentaire sur les congruences.
-/

import RevHalt.Trilemma.CofinalHornsSimple
import RevHalt.Trilemma.CofinalHornsPA

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

namespace Collatz

/-- Étape Collatz. -/
def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Itération Collatz : iter k seed = après k pas. -/
def iter : Nat → Nat → Nat
  | 0,     seed => seed
  | k + 1, seed => iter k (step seed)

/-- Lecture pure Collatz → Mode via mod 3. -/
def sigmaPure (seed : Nat) : Nat → Mode :=
  fun k =>
    let x := iter k seed
    if x % 3 = 0 then Mode.BC
    else if x % 3 = 1 then Mode.AC
    else Mode.AB

/--
\sigma mixte :
  - k%6=0 ↦ BC
  - k%6=1 ↦ AC
  - k%6=2 ↦ AB
  - k%6∈{3,4,5} ↦ sigmaPure seed k
-/
def sigmaMix (seed : Nat) : Nat → Mode :=
  fun k =>
    match k % 6 with
    | 0 => Mode.BC
    | 1 => Mode.AC
    | 2 => Mode.AB
    | _ => sigmaPure seed k

end Collatz

section CollatzDynamicPA

-- Contexte RevHalt / Trilemma
variable {Provable : Set PropT -> PropT -> Prop}
variable {K : RHKit}
variable {Machine : Code -> Trace}
variable {encode_halt : Code -> PropT}
variable {Cn : Set PropT -> Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}

-- Paramètres structurels
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

-- Seed Collatz et axiomes internes PA
variable (seed : Nat)
variable (PAax : Set PropT)

-- Raccourci local (attention : dépend de `seed`)
abbrev sigma : Nat → Mode := Collatz.sigmaMix seed

-- =============================
-- 1) Cofinalité des modes pour sigmaMix
-- =============================

/-- Forme pratique : witness explicite pour k%6 = r. -/
private def kResidue (N r : Nat) : Nat := 6 * N + r

private lemma kResidue_ge (N r : Nat) : N ≤ kResidue N r := by
  dsimp [kResidue]
  calc N ≤ 1 * N := (Nat.one_mul N).symm.le
       _ ≤ 6 * N := Nat.mul_le_mul_right N (by decide)
       _ ≤ 6 * N + r := Nat.le_add_right _ _

/-- sigmaMix est cofinal sur BC. -/
lemma sigmaMix_cofinal_BC : SigmaCofinal (sigma seed) Mode.BC := by
  intro N0
  -- witness index: 6*(N0+1)
  refine ⟨6 * (N0 + 1), ?_, ?_⟩
  · calc N0 ≤ N0 + 1 := Nat.le_succ N0
        _   ≤ 6 * (N0 + 1) := (kResidue_ge (N0+1) 0)
  · -- sigma (6*(N0+1)) = BC
    dsimp [sigma, Collatz.sigmaMix]
    -- (6*N0) % 6 = 0
    have : (6 * (N0 + 1)) % 6 = 0 := Nat.mul_mod_right 6 (N0 + 1)
    rw [this]

/-- sigmaMix est cofinal sur AC. -/
lemma sigmaMix_cofinal_AC : SigmaCofinal (sigma seed) Mode.AC := by
  intro N0
  refine ⟨6 * (N0 + 1) + 1, ?_, ?_⟩
  · calc N0 ≤ N0 + 1 := Nat.le_succ N0
        _   ≤ 6 * (N0 + 1) := Nat.le_mul_of_pos_left _ (by decide)
        _   ≤ 6 * (N0 + 1) + 1 := Nat.le_add_right _ _
  · dsimp [sigma, Collatz.sigmaMix]
    have : (6 * (N0 + 1) + 1) % 6 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rw [this]

/-- sigmaMix est cofinal sur AB. -/
lemma sigmaMix_cofinal_AB : SigmaCofinal (sigma seed) Mode.AB := by
  intro N0
  refine ⟨6 * (N0 + 1) + 2, ?_, ?_⟩
  · calc N0 ≤ N0 + 1 := Nat.le_succ N0
        _   ≤ 6 * (N0 + 1) := Nat.le_mul_of_pos_left _ (by decide)
        _   ≤ 6 * (N0 + 1) + 2 := Nat.le_add_right _ _
  · dsimp [sigma, Collatz.sigmaMix]
    have : (6 * (N0 + 1) + 2) % 6 = 2 := by
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rw [this]

-- =============================
-- 2) Théorème final : Collatz + DynamicPA Strong
-- =============================

/--
Théorème "Collatz + DynamicPA Strong" avec cofinalités internes.
-/
theorem collatz_dynamicPA_Strong_final
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
              (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB)) :
    let s : Nat → Mode := sigma seed
    let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
               (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
               (hIdem := hIdem) (hProvCn := hProvCn) PAax .BC witBC
    let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
               (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
               (hIdem := hIdem) (hProvCn := hProvCn) PAax .AC witAC
    let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine)
               (encode_halt := encode_halt) (Cn := Cn) (A0 := A0)
               (hIdem := hIdem) (hProvCn := hProvCn) PAax .AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 s hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 s hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 s hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := s) hIdem hProvCn PAax .BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := s) hIdem hProvCn PAax .AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := s) hIdem hProvCn PAax .AB witBC witAC witAB) := by
  have hBC : SigmaCofinal (sigma seed) .BC := sigmaMix_cofinal_BC seed
  have hAC : SigmaCofinal (sigma seed) .AC := sigmaMix_cofinal_AC seed
  have hAB : SigmaCofinal (sigma seed) .AB := sigmaMix_cofinal_AB seed
  simpa [sigma] using
    (dynamic_trilemma_with_PA_Strong_final
      (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma seed)
      (hIdem := hIdem) (hProvCn := hProvCn)
      PAax hMono hCnExt hBC hAC hAB witBC witAC witAB)

end CollatzDynamicPA

end RevHalt.Trilemma
