import RevHalt.Base.QuotientUp
import RevHalt.Theory.PrimitiveHolonomy

/-!
# RevHalt.Theory.HolonomyBridge

Small, axiom-free bridge lemmas between:
- `RevHalt.Base.QuotientUp.UpEqv` (pointwise equivalence of `up`-closures of traces), and
- `PrimitiveHolonomy.RelEq` (pointwise equivalence of relations).

This is meant as a *typing-level* correspondence: both projects avoid function equality
(`funext`/`propext`) by working with pointwise equivalence.
-/

namespace RevHalt

namespace HolonomyBridge

/-- View a trace `T : ℕ → Prop` as a binary relation `ℕ → PUnit → Prop`. -/
def TraceRel (T : Trace) : PrimitiveHolonomy.Relation ℕ PUnit :=
  fun n _ => T n

theorem relEq_traceRel_iff (T T' : Trace) :
    PrimitiveHolonomy.RelEq (TraceRel T) (TraceRel T') ↔ ∀ n : ℕ, T n ↔ T' n := by
  constructor
  · intro h n
    exact h n PUnit.unit
  · intro h n y
    cases y
    exact h n

theorem upEqv_iff_relEq_up (T T' : Trace) :
    UpEqv T T' ↔
      PrimitiveHolonomy.RelEq (TraceRel (up T)) (TraceRel (up T')) := by
  constructor
  · intro h n y
    cases y
    exact h n
  · intro h n
    exact h n PUnit.unit

end HolonomyBridge

end RevHalt

-- Axiom checks:
#print axioms RevHalt.HolonomyBridge.TraceRel
#print axioms RevHalt.HolonomyBridge.relEq_traceRel_iff
#print axioms RevHalt.HolonomyBridge.upEqv_iff_relEq_up

