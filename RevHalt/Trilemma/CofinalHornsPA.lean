import RevHalt.Trilemma.CofinalHornsSimple

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

section DynamicPA

-- 1) Context variables (declared once, no hiding)
variable {Provable : Set PropT -> PropT -> Prop}
variable {K : RHKit}
variable {Machine : Code -> Trace}
variable {encode_halt : Code -> PropT}
variable {Cn : Set PropT -> Set PropT}
variable {A0 : ThState (PropT := PropT) Provable Cn}
variable {sigma : Nat -> Mode}
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

-- 3) Definition: PA is "in" the state Gamma
def PA_in (PAax : Set PropT) (Γ : Set PropT) : Prop :=
  PAax ⊆ Γ

-- 4) PA at time n
def PA_at (PAax : Set PropT) (n : Nat) : Prop :=
  PA_in PAax (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ

-- 5) PairPA: The "Strong Bundle" Condition
def PairPA (PAax : Set PropT) (m : Mode) (n : Nat) : Prop :=
  Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn m n
  ∧ PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (hIdem := hIdem) (hProvCn := hProvCn) PAax n

-- 6) Witnesses conversions

/-- Helper: Convert PairPA witness to simple Pair witness.
    We explicitly unfold PairPA using projection .1 to access the left component. -/
def toSimpleWitness
    (PAax : Set PropT) (m : Mode)
    (w : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) (A0 := A0) hIdem hProvCn PAax m)) :
    CofinalWitness (Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn m) :=
  fun N =>
    ⟨ (w N).val
    , ⟨ (w N).property.1
      , (w N).property.2.1
      ⟩
    ⟩

-- 7) Times unfolding stability

lemma times_succ
    (witBC : CofinalWitness (Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn .BC))
    (witAC : CofinalWitness (Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn .AC))
    (witAB : CofinalWitness (Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn .AB))
    (k : Nat) :
    times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn witBC witAC witAB (k + 1) =
      match sigma (k+1) with
      | .BC => (witBC (times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn witBC witAC witAB k + 1)).val
      | .AC => (witAC (times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn witBC witAC witAB k + 1)).val
      | .AB => (witAB (times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn witBC witAC witAB k + 1)).val := by
  cases h : sigma (k+1) <;> simp [times, h]

-- 8) PA Cofinality on Visits

/-- PA reappears cofinally often *on visits of mode m*. -/
def CofinalPA_on_visits
    (PAax : Set PropT)
    (m : Mode)
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB)) : Prop :=
  let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC witBC
  let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC witAC
  let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB witAB
  CofinalK (fun k =>
    sigma k = m ∧
    PA_at (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) hIdem hProvCn PAax
      (times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k))

theorem cofinalPA_on_mode
    (PAax : Set PropT)
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB))
    (m : Mode)
    (hm : SigmaCofinal sigma m) :
    CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax m witBC witAC witAB := by
  -- helpers to simplify notation
  let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC witBC
  let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC witAC
  let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB witAB

  intro N
  -- Obtain a visit index k >= N
  rcases hm N with ⟨k, hk_ge, hk_mode⟩
  refine ⟨k, hk_ge, ?_⟩
  refine ⟨hk_mode, ?_⟩

  -- We need PA at t = times ... k.
  -- (removed unused t)

  -- Split cases on k to unfold `times`
  cases k with
  | zero =>
      -- t = times ... 0.
      simp only [times]
      -- sigma 0 = m. So we use witness for m at 0.
      rw [hk_mode]
      cases m <;> simp
      · exact (witBC 0).property.2.2
      · exact (witAC 0).property.2.2
      · exact (witAB 0).property.2.2
  | succ k' =>
      -- t = times ... (k'+1).
      let prev := times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k'

      -- Stabilize rewrites
      have hprev : times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k' = prev := rfl

      -- use the helper lemma to unfold times at succ with mode m
      rw [times_succ (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
          (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn wBC wAC wAB k']
      rw [hk_mode]
      cases m <;> simp [hprev]
      · exact (witBC (prev + 1)).property.2.2
      · exact (witAC (prev + 1)).property.2.2
      · exact (witAB (prev + 1)).property.2.2

-- 9) Final Theorem

theorem dynamic_trilemma_with_PA_Strong_final
    (PAax : Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBC : SigmaCofinal sigma .BC)
    (hAC : SigmaCofinal sigma .AC)
    (hAB : SigmaCofinal sigma .AB)
    (witBC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
              (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB)) :
    let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC witBC
    let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC witAC
    let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax .BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax .AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax .AB witBC witAC witAB) := by
  let wBC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .BC witBC
  let wAC := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AC witAC
  let wAB := toSimpleWitness (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
               (Cn := Cn) (A0 := A0) hIdem hProvCn PAax .AB witAB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cofinal_hornBC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hBC
  · exact cofinal_hornAC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAC
  · exact cofinal_hornAB_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAB
  · exact cofinalPA_on_mode (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax witBC witAC witAB .BC hBC
  · exact cofinalPA_on_mode (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax witBC witAC witAB .AC hAC
  · exact cofinalPA_on_mode (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) hIdem hProvCn
      PAax witBC witAC witAB .AB hAB

end DynamicPA
end RevHalt.Trilemma
