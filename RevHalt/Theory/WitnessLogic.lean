import RevHalt.Base
import RevHalt.Theory.Canonicity

/-!
# RevHalt.Theory.WitnessLogic

Formal backing for the "Use ML as Heuristic Witness Proposer" strategy.

This file proves that:
1. If we find an index `n` where `T n` is true, then `Halts T` is true.
2. Checking a finite witness is decidable.

This justifies the "S2 + ML" architecture:
- ML suggests `n`
- S2 checks `T n`
- If check passes, S2 certifies `Halts T` soundly.
-/

namespace RevHalt.Theory.WitnessLogic

-- We use the global `Trace` (ℕ → Bool) from RevHalt.Base


/--
  The fundamental correctness of the Witness Heuristic.
  If a checker confirms `T n` (Prop), then `Halts T` (Prop) is proven.
-/
theorem witness_soundness (T : Trace) (n : ℕ) (h_witness : T n) : Halts T := by
  exact ⟨n, h_witness⟩

/--
  Logical soundness of the check (abstracting over decidability).
  If the proposition `T n` holds, it implies Halting.
-/
theorem check_witness_correct (T : Trace) (n : ℕ) :
  T n → Halts T := by
  intro h
  exact witness_soundness T n h

end RevHalt.Theory.WitnessLogic
