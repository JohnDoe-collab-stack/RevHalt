import RevHalt.Theory.TheoryDynamics_Transfinite

namespace RevHalt.Bifurcation

universe u v
variable {PropT : Type u}
variable {Code  : Type u}

variable (Provable : Set PropT → PropT → Prop)
variable (K : RHKit)
variable (Machine : Code → Trace)
variable (encode_halt : Code → PropT)

-- We keep Cn explicit because structural_escape_transfinite quantifies over it.
variable (Cn : Set PropT → Set PropT)

-- Local / Global predicates (minimal, typed exactly as used by the escape theorem)

/-- Local event: absorption occurs at some successor stage strictly before `lim`. -/
def LocalBefore
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v}) : Prop :=
  ∃ β < lim,
    Absorbable Provable
      (transIter (F Provable K Machine encode_halt Cn) A0.Γ (β + 1))

/-- Frontier persistence at the limit (Route II regime at `lim`). -/
def FrontierAt
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v}) : Prop :=
  RouteIIApplies Provable K Machine encode_halt Cn
    (transIter (F Provable K Machine encode_halt Cn) A0.Γ lim)

/-- Global well-posedness at the limit: continuity of the union-limit operator at `lim`. -/
def GlobalContAt
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v}) : Prop :=
  ContinuousAt (PropT := PropT)
    (F Provable K Machine encode_halt Cn) A0.Γ lim


/-
Bifurcation theorem (transfinite, filled):

Under the standard RevHalt structural kernel, if (i) absorption occurs
before a successor-limit `lim` and (ii) the frontier persists at `lim`,
then continuity at `lim` is impossible.

Equivalently: LocalBefore ∧ FrontierAt ⇒ ¬ GlobalContAt.
-/
theorem bifurcation_transfinite
    (hMono  : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem  : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCord : ProvClosedDirectedOrd.{u, v} Provable)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hAbs : LocalBefore (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) A0 lim)
    (hRoute : FrontierAt (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) A0 lim) :
    ¬ GlobalContAt (Provable := Provable) (K := K) (Machine := Machine)
        (encode_halt := encode_halt) (Cn := Cn) A0 lim := by
  intro hCont
  -- Directly discharge by the existing escape theorem.
  exact structural_escape_transfinite
    (PropT := PropT) (Provable := Provable) (K := K) (Machine := Machine)
    (encode_halt := encode_halt)
    (Cn := Cn)
    (hMono := hMono) (hCnExt := hCnExt) (hIdem := hIdem) (hProvCn := hProvCn)
    (hPCord := hPCord)
    (A0 := A0) (lim := lim) (hLim := hLim)
    (hAbs := hAbs) (hRoute := hRoute) (hCont := hCont)


/-
Clean disjunctive form (your “totalité disjonctive”):

K ∧ LocalBefore ∧ FrontierAt ⇒ (¬ GlobalContAt).
(If you also want the pure propositional form ¬(Local ∧ Global), see below.)
-/
theorem not_local_and_global_cont
    (hMono  : ProvRelMonotone Provable)
    (hCnExt : CnExtensive Cn)
    (hIdem  : CnIdem Cn)
    (hProvCn : ProvClosedCn Provable Cn)
    (hPCord : ProvClosedDirectedOrd.{u, v} Provable)
    (A0 : ThState (PropT := PropT) Provable Cn)
    (lim : Ordinal.{v})
    (hLim : Order.IsSuccLimit lim)
    (hRoute : FrontierAt (Provable := Provable) (K := K) (Machine := Machine)
              (encode_halt := encode_halt) (Cn := Cn) A0 lim) :
    ¬ ( LocalBefore (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) A0 lim
      ∧ GlobalContAt (Provable := Provable) (K := K) (Machine := Machine)
          (encode_halt := encode_halt) (Cn := Cn) A0 lim ) := by
  intro h
  rcases h with ⟨hAbs, hCont⟩
  exact (bifurcation_transfinite
    (Provable := Provable) (K := K) (Machine := Machine) (encode_halt := encode_halt) (Cn := Cn)
    hMono hCnExt hIdem hProvCn hPCord A0 lim hLim hAbs hRoute) hCont

end RevHalt.Bifurcation
