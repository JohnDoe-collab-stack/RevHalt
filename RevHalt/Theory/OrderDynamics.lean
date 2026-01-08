import Mathlib.Order.Basic
import Mathlib.Order.Synonym

/-!
# RevHalt.Theory.OrderDynamics
...
-/
namespace RevHalt.OrderDynamics

variable {I : Type} [Preorder I]

/-- A property/trace over the index set I. -/
def Trace (I : Type) := I → Prop

variable (T : Trace I)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1. upPast: The Cumulative (Passé) Operator
-- ═══════════════════════════════════════════════════════════════════════════════

/--
`upPast T i`: True if T holds at some point `j ≤ i` in the past.
Formula: `∃ j ≤ i, T j`
-/
def upPast (i : I) : Prop := ∃ j ≤ i, T j

/--
**Monotonicity of upPast**:
If something happened in the past of `i`, and `i ≤ i'`,
then it happened in the past of `i'`.

Proof relies only on transitivity of `≤`.
-/
theorem upPast_mono {i i' : I} (h_le : i ≤ i') (h_past : upPast T i) : upPast T i' :=
  let ⟨j, hj_le, hT⟩ := h_past
  Exists.intro j (And.intro (le_trans hj_le h_le) hT)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2. upFut: The Stabilization (Future) Operator
-- ═══════════════════════════════════════════════════════════════════════════════

/--
`upFut T i`: True if T holds at some point `j ≥ i` in the future.
Formula: `∃ j ≥ i, T j`
This is exactly the condition `¬ Stabilizes T i` in the Collatz context.
-/
def upFut (i : I) : Prop := ∃ j ≥ i, T j

/--
**Antitonicity of upFut**:
If something is possible in the future of `i'`, and `i ≤ i'`,
then it is certainly possible in the future of `i`.

Proof: `j ≥ i'` and `i ≤ i'` implies `j ≥ i`.
-/
theorem upFut_antitone {i i' : I} (h_le : i ≤ i') (h_fut : upFut T i') : upFut T i :=
  let ⟨j, hj_ge, hT⟩ := h_fut
  Exists.intro j (And.intro (le_trans h_le hj_ge) hT)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3. Symmetry
-- ═══════════════════════════════════════════════════════════════════════════════

/--
upFut corresponds to upPast in the dual order (≥).
This confirms they are the same structural object, just viewed in opposite directions.
-/
theorem upFut_eq_upPast_dual :
    upFut T = upPast (I := Iᵒᵈ) T := by
  ext i
  rfl

end RevHalt.OrderDynamics
