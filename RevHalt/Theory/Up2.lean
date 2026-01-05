import RevHalt.Base.Trace
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

/-!
# RevHalt.Theory.Up2

## Π₂ Structural Closure (Up2)

This module defines Up2, the Π₂ analogue of RevHalt's `up` operator.

- **up (up1)**: Temporal closure on traces (Σ₁/Π₁ level)
- **Up2**: Structural closure on game trees (Σ₂/Π₂ level)
- **up1 ⊗ Up2**: Composition giving space×time closure

## Definition Strategy

Up2 is defined as the **least fixed point** (infimum of all closed sets),
which is axiom-free and constructive.

A set S is "Up2-closed" for certificates B if:
- B ⊆ S
- P-closure: turn p = P ∧ (∃q ∈ moves p, q ∈ S) → p ∈ S
- O-closure: turn p = O ∧ moves p ≠ ∅ ∧ (∀q ∈ moves p, q ∈ S) → p ∈ S

Then: Up2(B) := ⋂ { S | S is Up2-closed for B }
-/

namespace RevHalt.Up2

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) Game Interface
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Turn indicator: Proponent (∃) or Opponent (∀). -/
inductive Turn where
  | P : Turn  -- Proponent (existential choice)
  | O : Turn  -- Opponent (universal challenge)
deriving DecidableEq, Repr

/-- A Game interface for Up2. -/
structure Game where
  Pos : Type
  root : Pos
  turn : Pos → Turn
  moves : Pos → Set Pos

namespace Game

variable (G : Game)

/-- A position has no moves (terminal). -/
def isTerminal (p : G.Pos) : Prop := G.moves p = ∅

/-- A position has at least one move. -/
def hasMove (p : G.Pos) : Prop := (G.moves p).Nonempty

end Game

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) Up2-Closure: The Fixed Point Characterization
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A set S is **P-closed** at position p: if P can step to S, then p ∈ S.
-/
def PClosedAt (G : Game) (S : Set G.Pos) (p : G.Pos) : Prop :=
  G.turn p = Turn.P → (∃ q ∈ G.moves p, q ∈ S) → p ∈ S

/--
A set S is **O-closed** at position p: if all O-moves lead to S, then p ∈ S.
-/
def OClosedAt (G : Game) (S : Set G.Pos) (p : G.Pos) : Prop :=
  G.turn p = Turn.O → G.hasMove p → (∀ q ∈ G.moves p, q ∈ S) → p ∈ S

/--
A set S is **Up2-closed** for certificates B if:
1. B ⊆ S (base case)
2. P-closed everywhere
3. O-closed everywhere
-/
def Up2Closed (G : Game) (B : Set G.Pos) (S : Set G.Pos) : Prop :=
  B ⊆ S ∧ (∀ p, PClosedAt G S p) ∧ (∀ p, OClosedAt G S p)

/--
**Up2Set(B)**: The least Up2-closed set containing B.

Defined as the intersection of all Up2-closed sets.
This is axiom-free: it's the standard least fixed point construction.
-/
def Up2Set (G : Game) (B : Set G.Pos) : Set G.Pos :=
  { p | ∀ S, Up2Closed G B S → p ∈ S }

/-- Membership in Up2Set. -/
def Up2Mem (G : Game) (B : Set G.Pos) (p : G.Pos) : Prop :=
  p ∈ Up2Set G B

/-- Win at root: the root is in the winning region. -/
def Win (G : Game) (B : Set G.Pos) : Prop := Up2Mem G B G.root

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Up2Set is Up2-Closed (the least one)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Set.univ is Up2-closed (trivially). -/
theorem Up2Closed_univ (G : Game) (B : Set G.Pos) : Up2Closed G B Set.univ := by
  refine ⟨Set.subset_univ B, ?_, ?_⟩
  · intro p _ _; exact Set.mem_univ p
  · intro p _ _ _; exact Set.mem_univ p

/-- The family of Up2-closed sets is nonempty. -/
theorem Up2Closed_nonempty (G : Game) (B : Set G.Pos) :
    { S | Up2Closed G B S }.Nonempty :=
  ⟨Set.univ, Up2Closed_univ G B⟩

/-- Base rule: B ⊆ Up2Set(B). -/
theorem Up2Set_base (G : Game) (B : Set G.Pos) : B ⊆ Up2Set G B := by
  intro p hp S hS
  exact hS.1 hp

/-- P-step rule for Up2Set. -/
theorem Up2Set_stepP (G : Game) (B : Set G.Pos) (p : G.Pos) :
    G.turn p = Turn.P → (∃ q ∈ G.moves p, q ∈ Up2Set G B) → p ∈ Up2Set G B := by
  intro hTurn hex S hS
  apply hS.2.1 p hTurn
  obtain ⟨q, hqMove, hqUp2⟩ := hex
  exact ⟨q, hqMove, hqUp2 S hS⟩

/-- O-step rule for Up2Set. -/
theorem Up2Set_stepO (G : Game) (B : Set G.Pos) (p : G.Pos) :
    G.turn p = Turn.O → G.hasMove p →
    (∀ q ∈ G.moves p, q ∈ Up2Set G B) → p ∈ Up2Set G B := by
  intro hTurn hHas hall S hS
  apply hS.2.2 p hTurn hHas
  intro q hq
  exact hall q hq S hS

/-- Up2Set is Up2-closed. -/
theorem Up2Set_isClosed (G : Game) (B : Set G.Pos) : Up2Closed G B (Up2Set G B) := by
  refine ⟨Up2Set_base G B, ?_, ?_⟩
  · intro p; exact Up2Set_stepP G B p
  · intro p; exact Up2Set_stepO G B p

/-- Up2Set is the least Up2-closed set. -/
theorem Up2Set_least (G : Game) (B : Set G.Pos) (S : Set G.Pos) (hS : Up2Closed G B S) :
    Up2Set G B ⊆ S := by
  intro p hp
  exact hp S hS

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Basic Properties of Up2
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extensiveness: B ⊆ Up2Set(B). -/
theorem Up2_extensive (G : Game) (B : Set G.Pos) : B ⊆ Up2Set G B :=
  Up2Set_base G B

/-- Monotonicity: B ⊆ C → Up2Set(B) ⊆ Up2Set(C). -/
theorem Up2_mono (G : Game) {B C : Set G.Pos} (h : B ⊆ C) :
    Up2Set G B ⊆ Up2Set G C := by
  apply Up2Set_least
  refine ⟨Set.Subset.trans h (Up2Set_base G C), ?_, ?_⟩
  · intro p hTurn hex
    apply Up2Set_stepP G C p hTurn
    obtain ⟨q, hqMove, hqUp2⟩ := hex
    exact ⟨q, hqMove, hqUp2⟩
  · intro p hTurn hHas hall
    apply Up2Set_stepO G C p hTurn hHas
    exact hall

/-- Idempotence (left): Up2Set(Up2Set(B)) ⊆ Up2Set(B). Axiom-free. -/
theorem Up2_idem_subset (G : Game) (B : Set G.Pos) :
    Up2Set G (Up2Set G B) ⊆ Up2Set G B := by
  intro p hp S hS
  have hSClosed : Up2Closed G (Up2Set G B) S := by
    refine ⟨?_, hS.2.1, hS.2.2⟩
    exact Up2Set_least G B S hS
  exact hp S hSClosed

/-- Idempotence (right): Up2Set(B) ⊆ Up2Set(Up2Set(B)). Axiom-free. -/
theorem Up2_idem_supset (G : Game) (B : Set G.Pos) :
    Up2Set G B ⊆ Up2Set G (Up2Set G B) :=
  Up2_mono G (Up2Set_base G B)

/-- Idempotence as bi-membership: p ∈ Up2Set(Up2Set(B)) ↔ p ∈ Up2Set(B). Axiom-free. -/
theorem Up2_idem_iff (G : Game) (B : Set G.Pos) (p : G.Pos) :
    p ∈ Up2Set G (Up2Set G B) ↔ p ∈ Up2Set G B :=
  ⟨fun h => Up2_idem_subset G B h, fun h => Up2_idem_supset G B h⟩

/-- Idempotence as equality. Uses propext/Quot.sound for set equality. -/
theorem Up2_idem (G : Game) (B : Set G.Pos) :
    Up2Set G (Up2Set G B) = Up2Set G B :=
  Set.Subset.antisymm (Up2_idem_subset G B) (Up2_idem_supset G B)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Fibered Traces: a trace at each position
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A fibered trace family: a trace at each position. -/
def FiberedTrace (G : Game) := G.Pos → RevHalt.Trace

/-- Local success predicate: ∃k, T p k (Σ₁ witness). -/
def Good (G : Game) (T : FiberedTrace G) (p : G.Pos) : Prop :=
  ∃ k, T p k

/-- The set of positions with local success. -/
def GoodSet (G : Game) (T : FiberedTrace G) : Set G.Pos :=
  { p | Good G T p }

/-- Alternative: Good via Halts. -/
theorem Good_iff_Halts (G : Game) (T : FiberedTrace G) (p : G.Pos) :
    Good G T p ↔ RevHalt.Halts (T p) := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Composition: up1 ⊗ Up2
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**The composed operator (up1 ⊗ Up2)(T, B)**.

Success = reaching either:
- A structurally certified position (in B), or
- A position with a finite temporal witness (Good p)

Then propagate via Up2 (∃/∀ alternation).
-/
def CompUp (G : Game) (T : FiberedTrace G) (B : Set G.Pos) : Set G.Pos :=
  Up2Set G (GoodSet G T ∪ B)

/-- Win under composition. -/
def CompWin (G : Game) (T : FiberedTrace G) (B : Set G.Pos) : Prop :=
  G.root ∈ CompUp G T B

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) O-Strategy and Avoidance
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An O-strategy: at O-positions with moves, choose a successor. -/
structure OStrategy (G : Game) where
  choice : (p : G.Pos) → G.turn p = Turn.O → G.hasMove p → G.Pos
  valid : ∀ p hTurn hHas, choice p hTurn hHas ∈ G.moves p

/--
**Avoid(S, p)**: Opponent can prevent reaching S.

There exists an O-strategy such that all compatible plays avoid S.
The condition `p ∉ S` is included to ensure Avoid is false for positions already in S.
-/
def Avoid (G : Game) (S : Set G.Pos) (p : G.Pos) : Prop :=
  p ∉ S ∧ ∃ τ : OStrategy G, ∀ (seq : ℕ → G.Pos),
    seq 0 = p →
    (∀ n, seq (n + 1) ∈ G.moves (seq n)) →
    (∀ n, (hTurn : G.turn (seq n) = Turn.O) → (hHas : G.hasMove (seq n)) →
      seq (n + 1) = τ.choice (seq n) hTurn hHas) →
    ∀ n, seq n ∉ S

/-- The kernel of Up2: positions where Avoid holds. -/
def Kernel (G : Game) (S : Set G.Pos) : Set G.Pos :=
  { p | Avoid G S p }

/-- Kernel of the composed operator. -/
def CompKernel (G : Game) (T : FiberedTrace G) (B : Set G.Pos) : Set G.Pos :=
  Kernel G (GoodSet G T ∪ B)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Open Determinacy (Capability)
-- ═══════════════════════════════════════════════════════════════════════════════

/--
**Open Determinacy**: For reachability games, either P wins or O can avoid.

This is the Π₂ analogue of EM for the Σ₁/Π₁ dichotomy.
-/
def DetOpen (G : Game) : Prop :=
  ∀ (S : Set G.Pos) (p : G.Pos), Up2Mem G S p ∨ Avoid G S p

/-- The dichotomy theorem: DetOpen gives dichotomy. -/
theorem dichotomy_of_DetOpen (G : Game) (hDet : DetOpen G) (S : Set G.Pos) (p : G.Pos) :
    Up2Mem G S p ∨ Avoid G S p :=
  hDet S p

-- ═══════════════════════════════════════════════════════════════════════════════
-- 9) Degenerate Case: Deterministic Games
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A game is deterministic if every position has at most one move. -/
def Deterministic (G : Game) : Prop :=
  ∀ p, ∀ q₁ q₂, q₁ ∈ G.moves p → q₂ ∈ G.moves p → q₁ = q₂

/-- For deterministic games, the O-step rule becomes vacuous. -/
theorem deterministic_O_choice_unique (G : Game) (hDet : Deterministic G)
    (p : G.Pos) (q : G.Pos) (hq : q ∈ G.moves p) :
    ∀ r ∈ G.moves p, r = q := by
  intro r hr
  exact hDet p r q hr hq

-- ═══════════════════════════════════════════════════════════════════════════════
-- 10) Up2Kit: The Kit-Level Abstraction (Parallel to RHKit)
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Up2Kit: Kit-Level Abstraction for Π₂

This section parallels the Σ₁/Π₁ architecture:

| Σ₁/Π₁ (up1) | Π₂ (Up2) |
|-------------|----------|
| `RHKit.proj` | `Up2Kit.eval` |
| `Rev0_K K T` | `WinK K G S p` |
| `KitStabilizes K T` | `AvoidK K G S p` |
| `DetectsMonotone K` | `DetectsWin K` |
| `T1_traces` | `T1_Up2` |
| `T1_stabilization` | `T1_Avoid` |
-/

/--
**Up2Kit**: An abstract observation mechanism for game positions.

Parallel to `RHKit` for traces, but for games.
-/
structure Up2Kit (G : Game) where
  /-- Projection function: determines Win/Avoid verdict. -/
  eval : Set G.Pos → G.Pos → Bool

/-- Kit-level positive verdict: the Kit says "P wins from p". -/
def WinK (K : Up2Kit G) (S : Set G.Pos) (p : G.Pos) : Prop :=
  K.eval S p = true

/-- Kit-level negative verdict: the Kit says "O can avoid from p". -/
def AvoidK (K : Up2Kit G) (S : Set G.Pos) (p : G.Pos) : Prop :=
  ¬ WinK K S p

/-- A Kit is correct if WinK implies Up2Mem (soundness). -/
def KitSound (K : Up2Kit G) : Prop :=
  ∀ S p, WinK K S p → Up2Mem G S p

/-- A Kit is complete if Up2Mem implies WinK (completeness). -/
def KitComplete (K : Up2Kit G) : Prop :=
  ∀ S p, Up2Mem G S p → WinK K S p

/--
**DetectsWin**: A Kit correctly detects winning positions.

This is the Up2 analogue of `DetectsMonotone` for RHKit.
-/
def DetectsWin (K : Up2Kit G) : Prop :=
  KitSound K ∧ KitComplete K

/--
**T1 for Up2**: If the Kit detects wins correctly,
then WinK ↔ Up2Mem (semantic truth).

Parallel to `T1_traces : Rev0_K K T ↔ Halts T`.
-/
theorem T1_Up2 (K : Up2Kit G) (hK : DetectsWin K) (S : Set G.Pos) (p : G.Pos) :
    WinK K S p ↔ Up2Mem G S p := by
  constructor
  · exact hK.1 S p
  · exact hK.2 S p

/--
**T1 for Avoid**: If the Kit detects wins correctly,
then AvoidK ↔ ¬Up2Mem.

Parallel to `T1_stabilization : KitStabilizes K T ↔ Stabilizes T`.
-/
theorem T1_Avoid_neg_noPropext (K : Up2Kit G) (hK : DetectsWin K)
    (S : Set G.Pos) (p : G.Pos) :
    AvoidK K S p ↔ ¬ Up2Mem G S p := by
  constructor
  · intro hAvoidK hUp2
    have hWin : WinK K S p := hK.2 S p hUp2
    exact hAvoidK hWin
  · intro hNotUp2 hWin
    have hUp2 : Up2Mem G S p := hK.1 S p hWin
    exact hNotUp2 hUp2

/--
**Key Lemma**: The complement of Avoid is Up2-closed.

The intuition:
- If q ∈ S, O cannot avoid S from q (fails at step 0)
- If turn q = P and ∃r where ¬Avoid(r), then ¬Avoid(q) (P moves there)
- If turn q = O and ∀r ¬Avoid(r), then ¬Avoid(q) (wherever O goes)

The proof requires formalizing plays and strategy composition,
which is non-trivial. We mark it as an axiom for now.

-- ═══════════════════════════════════════════════════════════════════════════════
-- 8) Structural Avoidance (Avoid2Set): The Axiom-Free Dual
-- ═══════════════════════════════════════════════════════════════════════════════


One-step safety condition for O to avoid reaching S forever, relative to candidate set X.

Interpretation:
- p must not already be in S
- if turn p = P, then ALL moves must stay in X (P can choose any move)
- if turn p = O and hasMove p, then O must have SOME move staying in X
  (if hasMove p is false, the implication is vacuous, so terminal positions not in S are safe)
-/
def AvoidStep (G : Game) (S X : Set G.Pos) : Set G.Pos :=
  { p |
      p ∉ S ∧
      (G.turn p = Turn.P → ∀ q, q ∈ G.moves p → q ∈ X) ∧
      (G.turn p = Turn.O → G.hasMove p → ∃ q, q ∈ G.moves p ∧ q ∈ X) }

/-- Post-fixed points for AvoidStep: X ⊆ AvoidStep(S,X). -/
def AvoidClosed (G : Game) (S X : Set G.Pos) : Prop :=
  X ⊆ AvoidStep G S X

/--
Greatest post-fixed point, given as the union of all post-fixed points.

Membership form (more convenient than `sUnion`):
p ∈ Avoid2Set  iff  ∃ X, AvoidClosed(S,X) ∧ p ∈ X
-/
def Avoid2Set (G : Game) (S : Set G.Pos) : Set G.Pos :=
  { p | ∃ X : Set G.Pos, AvoidClosed G S X ∧ p ∈ X }

/-- Abbreviation. -/
def Avoid2Mem (G : Game) (S : Set G.Pos) (p : G.Pos) : Prop :=
  p ∈ Avoid2Set G S

/-- The “not avoid2” region. -/
def NotAvoid2Set (G : Game) (S : Set G.Pos) : Set G.Pos :=
  { p | p ∉ Avoid2Set G S }

/-- Any post-fixed X is contained in Avoid2Set (by witnessing itself). -/
theorem Avoid2Set_largest (G : Game) (S X : Set G.Pos) (hX : AvoidClosed G S X) :
    X ⊆ Avoid2Set G S := by
  intro p hp
  exact ⟨X, hX, hp⟩

/-- Avoid2Set itself is post-fixed: Avoid2Set ⊆ AvoidStep(S, Avoid2Set). -/
theorem Avoid2Set_isClosed (G : Game) (S : Set G.Pos) :
    AvoidClosed G S (Avoid2Set G S) := by
  intro p hp
  rcases hp with ⟨X, hXclosed, hpX⟩
  have hpStep : p ∈ AvoidStep G S X := hXclosed hpX
  rcases hpStep with ⟨hpNS, hpP, hpO⟩
  refine ⟨hpNS, ?_, ?_⟩
  · intro hTurn q hqMove
    have hqX : q ∈ X := hpP hTurn q hqMove
    exact ⟨X, hXclosed, hqX⟩
  · intro hTurn hHas
    rcases hpO hTurn hHas with ⟨q, hqMove, hqX⟩
    refine ⟨q, hqMove, ?_⟩
    exact ⟨X, hXclosed, hqX⟩

/-- Avoid2Set is disjoint from S: Avoid2Set ⊆ Sᶜ (axiom-free). -/
theorem Avoid2Set_subset_compl (G : Game) (S : Set G.Pos) :
    Avoid2Set G S ⊆ { p | p ∉ S } := by
  intro p hp
  rcases hp with ⟨X, hXclosed, hpX⟩
  have hpStep : p ∈ AvoidStep G S X := hXclosed hpX
  exact hpStep.1

/--
`NotAvoid2Set` is Up2-closed for base S.

This replaces the axiom `notAvoid_isClosed` with a structural theorem.
It shows that the complement of the safety region is a winning region.
-/
theorem notAvoid2_isClosed (G : Game) (S : Set G.Pos) :
    Up2Closed G S (NotAvoid2Set G S) := by
  refine ⟨?base, ?pstep, ?ostep⟩

  · -- base: S ⊆ NotAvoid2Set
    intro p hpS hpAvoid2
    have : p ∉ S := (Avoid2Set_subset_compl G S) hpAvoid2
    exact this hpS

  · -- P-closure: if P can step to NotAvoid2Set, then p ∈ NotAvoid2Set
    intro p hTurn hex hpAvoid2
    rcases hpAvoid2 with ⟨X, hXclosed, hpX⟩
    have hpStep : p ∈ AvoidStep G S X := hXclosed hpX
    rcases hex with ⟨q, hqMove, hqNotAvoid2⟩
    have hqX : q ∈ X := (hpStep.2.1) hTurn q hqMove
    have : q ∈ Avoid2Set G S := ⟨X, hXclosed, hqX⟩
    exact hqNotAvoid2 this

  · -- O-closure: if O has a move and all moves are in NotAvoid2Set, then p ∈ NotAvoid2Set
    intro p hTurn hHas hall hpAvoid2
    rcases hpAvoid2 with ⟨X, hXclosed, hpX⟩
    have hpStep : p ∈ AvoidStep G S X := hXclosed hpX
    rcases (hpStep.2.2) hTurn hHas with ⟨q, hqMove, hqX⟩
    have hAvoid2 : q ∈ Avoid2Set G S := ⟨X, hXclosed, hqX⟩
    have hNotAvoid2 : q ∈ NotAvoid2Set G S := hall q hqMove
    exact hNotAvoid2 hAvoid2

/--
Axiom-free: Up2 winning implies not in Avoid2Set.

This replaces `Up2Mem_imp_not_Avoid` without needing any axiom.
-/
theorem Up2Mem_imp_not_Avoid2 (G : Game) (S : Set G.Pos) (p : G.Pos) :
    Up2Mem G S p → p ∉ Avoid2Set G S := by
  intro hUp2
  have hClosed : Up2Closed G S (NotAvoid2Set G S) := notAvoid2_isClosed G S
  have hLeast : Up2Set G S ⊆ NotAvoid2Set G S := Up2Set_least G S (NotAvoid2Set G S) hClosed
  exact hLeast hUp2

/--
Structural open determinacy: either P wins (Up2) or p is in the greatest safety region Avoid2Set.
No strategy objects needed here.
-/
def DetOpen2 (G : Game) : Prop :=
  ∀ (S : Set G.Pos) (p : G.Pos), Up2Mem G S p ∨ p ∈ Avoid2Set G S

/--
The dual trivial direction: Avoid2 implies not Up2.
Always axiom-free (relies on Up2Mem_imp_not_Avoid2).
-/
theorem Avoid2Mem_imp_not_Up2Mem (G : Game) (S : Set G.Pos) (p : G.Pos) :
    Avoid2Mem G S p → ¬ Up2Mem G S p := by
  intro hA2 hUp2
  exact (Up2Mem_imp_not_Avoid2 (G:=G) S p hUp2) hA2

/--
**Kernel Theorem for Π₂**:
Under open determinacy (`DetOpen2`), the structural kernel `Avoid2Set`
exactly captures the failure of `Up2Mem`.

`p ∈ Avoid2Set ↔ ¬ Up2Mem`

This is the Π₂ analogue of `up_eq_bot_iff` (stabilization).
-/
theorem kernel_iff_of_DetOpen2 (G : Game) (hDet : DetOpen2 G) (S : Set G.Pos) (p : G.Pos) :
    (p ∈ Avoid2Set G S) ↔ ¬ Up2Mem G S p := by
  constructor
  · exact Avoid2Mem_imp_not_Up2Mem (G:=G) S p
  · intro hNotUp2
    cases hDet S p with
    | inl hUp2 => exact False.elim (hNotUp2 hUp2)
    | inr hA2  => exact hA2

/--
**T1 for Avoid2 + DetOpen2**: If the Kit detects wins correctly
AND we have strict Structural Determinacy, then AvoidK ↔ Avoid2Mem.

This is the full T1 theorem for the structural negative form.
DetOpen2 is necessary to connect ¬Up2Mem to the structural Avoid2Set.
-/
theorem T1_Avoid2_noPropext (K : Up2Kit G) (hK : DetectsWin K) (hDet : DetOpen2 G)
    (S : Set G.Pos) (p : G.Pos) :
    AvoidK K S p ↔ Avoid2Mem G S p := by
  constructor
  · intro hAvoidK
    have hNotUp2 : ¬ Up2Mem G S p := by
      intro hUp2
      have hWin : WinK K S p := hK.2 S p hUp2
      exact hAvoidK hWin
    cases hDet S p with
    | inl hUp2 => exact False.elim (hNotUp2 hUp2)
    | inr hAvoid2 => exact hAvoid2
  · intro hAvoid2 hWin
    have hUp2 : Up2Mem G S p := hK.1 S p hWin
    have hNotAvoid2 : p ∉ Avoid2Set G S := Up2Mem_imp_not_Avoid2 (G:=G) S p hUp2
    exact hNotAvoid2 hAvoid2

/--
**Kernel Detector Theorem for Up2**:
A valid Kit detects exactly when a position belongs to the kernel.

Parallel to `KitStabilizes_iff_up_eq_bot`.
-/
theorem AvoidK_iff_not_in_Up2Set_noPropext (K : Up2Kit G) (hK : DetectsWin K)
    (S : Set G.Pos) (p : G.Pos) :
    AvoidK K S p ↔ p ∉ Up2Set G S := by
  -- unfold Up2Mem if you want, but Up2Mem was defeq membership
  simpa [Up2Mem] using (T1_Avoid_neg_noPropext (G:=G) K hK S p)

-- ═══════════════════════════════════════════════════════════════════════════════
-- Summary
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Summary: The Π₂ Module (Strictly Structurel)

### Definition
Up2 is defined as the **least fixed point**:
```
Up2Set(S) := { p | ∀ X, Up2Closed G S X → p ∈ X }
```
This is completely axiom-free.

### The Negative Dual
Avoid2Set is defined as the **greatest post-fixed point**:
```
Avoid2Set(S) := { p | ∃ X, AvoidClosed G S X ∧ p ∈ X }
```
This is completely axiom-free.

### Bridge
`notAvoid2_isClosed` proves structurally that `NotAvoid2Set` is Up2-closed.
This gives `Up2Mem → ¬Avoid2Mem` without axioms.

### Determinacy
`DetOpen2` asserts `∀ p, Up2Mem p ∨ Avoid2Mem p`.
This is the structural form of Π₂-determinacy.

### Objects Defined
- `Game`: interface (Pos, root, turn, moves)
- `Up2Closed`: closure predicate for sets
- `Up2Set`: winning region (lfp)
- `Avoid2Set`: safety region (gfp)
- `FiberedTrace`: trace family at each position
- `Good`/`GoodSet`: local Σ₁ success
- `OStrategy`/`Avoid`: (Legacy) strategy objects, not used in core kernel
- `DetOpen2`: structural open determinacy

### Key Theorems (all axiom-free except propext)
- `Up2_idem_iff`: axiom-free idempotence
- `notAvoid2_isClosed`: axiom-free dual closure
- `T1_Up2`: axiom-free Kit correctness
- `T1_Avoid2`: axiom-free negative correctness (under DetOpen2)
-/

end RevHalt.Up2

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Up2.Up2Closed_univ
#print axioms RevHalt.Up2.Up2Set_base
#print axioms RevHalt.Up2.Up2Set_stepP
#print axioms RevHalt.Up2.Up2Set_stepO
#print axioms RevHalt.Up2.Up2Set_isClosed
#print axioms RevHalt.Up2.Up2Set_least
#print axioms RevHalt.Up2.Up2_extensive
#print axioms RevHalt.Up2.Up2_mono
#print axioms RevHalt.Up2.Up2_idem_subset   -- axiom-free
#print axioms RevHalt.Up2.Up2_idem_supset   -- axiom-free
#print axioms RevHalt.Up2.Up2_idem_iff      -- axiom-free
#print axioms RevHalt.Up2.Up2_idem          -- uses propext (for set equality)
#print axioms RevHalt.Up2.Good_iff_Halts
#print axioms RevHalt.Up2.deterministic_O_choice_unique

-- Structural Dual theorems
#print axioms RevHalt.Up2.Avoid2Set_largest     -- axiom-free
#print axioms RevHalt.Up2.Avoid2Set_isClosed    -- axiom-free
#print axioms RevHalt.Up2.Avoid2Set_subset_compl -- axiom-free
#print axioms RevHalt.Up2.notAvoid2_isClosed    -- axiom-free
#print axioms RevHalt.Up2.Up2Mem_imp_not_Avoid2 -- axiom-free
#print axioms RevHalt.Up2.Avoid2Mem_imp_not_Up2Mem -- axiom-free
#print axioms RevHalt.Up2.kernel_iff_of_DetOpen2   -- axiom-free

-- Up2Kit theorems
#print axioms RevHalt.Up2.T1_Up2                      -- axiom-free
#print axioms RevHalt.Up2.T1_Avoid_neg_noPropext      -- axiom-free
#print axioms RevHalt.Up2.T1_Avoid2_noPropext         -- axiom-free
#print axioms RevHalt.Up2.AvoidK_iff_not_in_Up2Set_noPropext -- axiom-free
