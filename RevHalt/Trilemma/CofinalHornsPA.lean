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

-- 7) Redefine CofinalPA_along_times
--    We use CofinalK (phases) as requested, checking PA_at along `times`.
--    Note: `times` relies on the simple witnesses derived from the strong ones.
def CofinalPA_along_times_Strong
    (Provable : Set PropT -> PropT -> Prop) (K : RHKit) (Machine : Code -> Trace)
    (encode_halt : Code -> PropT) (Cn : Set PropT -> Set PropT) (A0 : ThState Provable Cn)
    (sigma : Nat -> Mode)
    (PAax : Set PropT)
    (hIdem : CnIdem Cn) (hProvCn : ProvClosedCn Provable Cn)
    (witBC_strong : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .BC))
    (witAC_strong : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AC))
    (witAB_strong : CofinalWitness (PairPA Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax .AB)) : Prop :=
  CofinalK (fun k =>
    let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC_strong
    let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC_strong
    let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB_strong
    let t := times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k
    PA_at Provable K Machine encode_halt Cn A0 hIdem hProvCn PAax t
  )

/--
The "Dynamic Disjunctive Totality" Theorem (Strong Bundle version).

If `sigma` visits modes cofinally, AND we have witnesses for (Pair ∧ PA),
then we obtain:
  1. The cofinality of each Horn (BC, AC, AB),
  2. The cofinality of PA along the same trajectory, AS A DIRECT CONSEQUENCE.

We verify PA is "imposed by the dynamic" because it's baked into the witnesses.
No independent `hPA` hypothesis is needed.
-/
theorem dynamic_trilemma_with_PA_Strong
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
    (CofinalPA_along_times_Strong Provable K Machine encode_halt Cn A0 sigma PAax hIdem hProvCn witBC witAC witAB) := by
  -- Define local shortcuts to match the statement's let-bindings
  let wBC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .BC witBC
  let wAC := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AC witAC
  let wAB := toSimpleWitness Provable K Machine encode_halt Cn A0 PAax hIdem hProvCn .AB witAB

  refine ⟨?_, ?_, ?_, ?_⟩

  -- 1) Horn BC
  · exact cofinal_hornBC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hBC

  -- 2) Horn AC
  · exact cofinal_hornAC_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAC

  -- 3) Horn AB
  · exact cofinal_hornAB_along_times Provable K Machine encode_halt Cn A0 sigma hMono hCnExt hIdem hProvCn wBC wAC wAB hAB

  -- 4) PA Cofinality (Proven, not Assumed)
  · intro K0
    rcases hBC K0 with ⟨k, hk_ge, hk_mode⟩
    exists k
    constructor
    · exact hk_ge
    · -- The time t is defined by `times`.
      -- We show that at this time, PA holds because the witness `witBC` enforces it.
      -- unfold CofinalPA_along_times_Strong
      dsimp

      -- Splitting cases on k determines how `times` is evaluated
      cases k with
      | zero =>
        simp [times, hk_mode]
        exact (witBC 0).property.right.right
      | succ k' =>
        simp [times, hk_mode]
        let prev := times Provable K Machine encode_halt Cn A0 sigma hIdem hProvCn wBC wAC wAB k'
        exact (witBC (prev + 1)).property.right.right

end DynamicPA

end RevHalt.Trilemma
