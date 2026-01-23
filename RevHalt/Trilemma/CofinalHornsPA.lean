import RevHalt.Trilemma.CofinalHornsSimple

namespace RevHalt.Trilemma

universe u
variable {PropT : Type u} {Code : Type u}

section DynamicPA

-- 1) Context variables (declared for types, but we will pass explicitly)
variable (Provable : Set PropT -> PropT -> Prop)
variable (K : RHKit)
variable (Machine : Code -> Trace)
variable (encode_halt : Code -> PropT)
variable (Cn : Set PropT -> Set PropT)
variable (A0 : ThState (PropT := PropT) Provable Cn)
variable (sigma : Nat -> Mode)

-- 3) Definition: PA is "in" the state Gamma (Inclusion style)
def PA_in (PAax : Set PropT) (Γ : Set PropT) : Prop :=
  PAax ⊆ Γ

-- 4) PA at time n
variable (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)

def PA_at (PAax : Set PropT) (n : Nat) : Prop :=
  PA_in PAax (chainState Provable K Machine encode_halt Cn hIdem hProvCn A0 n).Γ

-- 5) PairPA: The "Strong Bundle" Condition
def PairPA (PAax : Set PropT) (m : Mode) (n : Nat) : Prop :=
  Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn m n
  ∧ PA_at Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax n

-- 6) Witnesses for the Strong Bundle (PairPA)

/--
Helper: Convert Strong Witnesses (PairPA) to Simple Witnesses (Pair).
This allows us to reuse the existing `times` machinery which only requires `Pair`.
Since CofinalWitness is constructive (returns a Subtype), this projection is constructive
and computationally preserves the witness index `n`.
-/
def toSimpleWitness
    (Provable : Set PropT -> PropT -> Prop) (K : RHKit) (Machine : Code -> Trace)
    (encode_halt : Code -> PropT) (Cn : Set PropT -> Set PropT) (A0 : ThState Provable Cn)
    (PAax : Set PropT)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (m : Mode)
    (w : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax m)) :
    CofinalWitness (Pair Provable K Machine encode_halt Cn A0 hIdem hProvCn m) :=
  fun N =>
    ⟨(w N).val, (w N).property.left, (w N).property.right.left⟩

/-- PA reappears cofinally often *on visits of mode m*. -/
def CofinalPA_on_visits
    (PAax : Set PropT)
    (m : Mode)
    (witBC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) : Prop :=
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB
  CofinalK (fun k =>
    sigma k = m ∧
    PA_at Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax
      (times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k))

theorem cofinalPA_on_BC
    (PAax : Set PropT)
    (hBC : SigmaCofinal sigma .BC)
    (witBC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) :
    CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .BC witBC witAC witAB := by
  -- set the projected simple witnesses once
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB

  -- unfold target
  intro K0
  rcases hBC K0 with ⟨k, hk_ge, hk_mode⟩
  refine ⟨k, hk_ge, ?_⟩
  refine ⟨hk_mode, ?_⟩

  -- Let t be the time selected at phase k
  let t :=
    times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k

  -- Show PA holds at time t using the strong witness for BC
  -- Key point: by construction of `times`, at phase k when sigma k = BC,
  -- the time t is exactly the `n` returned by `witBC` (at some bound), hence PA comes from the witness.
  --
  -- Robust way: unfold `times` only one step using `hk_mode`.
  cases k with
  | zero =>
      simp [t, times, hk_mode, PA_at, PA_in]
      exact (witBC 0).property.right.right
  | succ k' =>
      -- Here: times (k'+1) uses witness at bound (times k' + 1)
      simp [t, times, hk_mode, PA_at, PA_in]
      -- after simp, goal is PA_in ... at witness-returned index:
      -- it is exactly the PA component of the strong witness at that bound
      let prev :=
        times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k'
      exact (witBC (prev + 1)).property.right.right

theorem cofinalPA_on_AC
    (PAax : Set PropT)
    (hAC : SigmaCofinal sigma .AC)
    (witBC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) :
    CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .AC witBC witAC witAB := by
  -- set the projected simple witnesses once
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB

  -- unfold target
  intro K0
  rcases hAC K0 with ⟨k, hk_ge, hk_mode⟩
  refine ⟨k, hk_ge, ?_⟩
  refine ⟨hk_mode, ?_⟩

  -- Let t be the time selected at phase k
  let t :=
    times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k

  -- Robust way: unfold `times` only one step using `hk_mode`.
  cases k with
  | zero =>
      simp [t, times, hk_mode, PA_at, PA_in]
      exact (witAC 0).property.right.right
  | succ k' =>
      -- Here: times (k'+1) uses witness at bound (times k' + 1)
      simp [t, times, hk_mode, PA_at, PA_in]
      -- after simp, goal is PA_in ... at witness-returned index:
      -- it is exactly the PA component of the strong witness at that bound
      let prev :=
        times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k'
      exact (witAC (prev + 1)).property.right.right

theorem cofinalPA_on_AB
    (PAax : Set PropT)
    (hAB : SigmaCofinal sigma .AB)
    (witBC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) :
    CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .AB witBC witAC witAB := by
  -- set the projected simple witnesses once
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB

  -- unfold target
  intro K0
  rcases hAB K0 with ⟨k, hk_ge, hk_mode⟩
  refine ⟨k, hk_ge, ?_⟩
  refine ⟨hk_mode, ?_⟩

  -- Let t be the time selected at phase k
  let t :=
    times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k

  -- Robust way: unfold `times` only one step using `hk_mode`.
  cases k with
  | zero =>
      simp [t, times, hk_mode, PA_at, PA_in]
      exact (witAB 0).property.right.right
  | succ k' =>
      -- Here: times (k'+1) uses witness at bound (times k' + 1)
      simp [t, times, hk_mode, PA_at, PA_in]
      -- after simp, goal is PA_in ... at witness-returned index:
      -- it is exactly the PA component of the strong witness at that bound
      let prev :=
        times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k'
      exact (witAB (prev + 1)).property.right.right

theorem dynamic_trilemma_with_PA_Strong_final
    (PAax : Set PropT)
    (hMono : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hBC : SigmaCofinal sigma .BC)
    (hAC : SigmaCofinal sigma .AC)
    (hAB : SigmaCofinal sigma .AB)
    (witBC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) :
    let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
    let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
    let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB
    (CofinalN (HornBC_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAC_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalN (HornAB_at_time Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB)) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .BC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .AC witBC witAC witAB) ∧
    (CofinalPA_on_visits (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax .AB witBC witAC witAB) := by
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cofinal_hornBC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hBC
  · exact cofinal_hornAC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAC
  · exact cofinal_hornAB_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAB
  · exact cofinalPA_on_BC (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax hBC witBC witAC witAB
  · exact cofinalPA_on_AC (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax hAC witBC witAC witAB
  · exact cofinalPA_on_AB (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt)
      (Cn := Cn) (A0 := A0) (sigma := sigma) (hIdem := hIdem) (hProvCn := hProvCn)
      PAax hAB witBC witAC witAB

end DynamicPA

end RevHalt.Trilemma
