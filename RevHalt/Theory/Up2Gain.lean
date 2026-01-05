import Mathlib.Data.Nat.Basic

/-!
# RevHalt.Theory.Up2Gain (Axiom-Free Version)

This module implements the **Up2Gain** extension using pure predicates (no Sets).
All definitions are designed to be **axiom-free** (`#print axioms` shows no dependencies).

It provides:
1.  **R1 Interface**: A mechanical checker for "Window Certificates".
2.  **Predicate-based Game**: Moves and turns defined as predicates.
3.  **Structural Closure**: Up2-like closure defined locally.
-/

namespace RevHalt.Up2Gain

-- ═══════════════════════════════════════════════════════════════════════════════
-- 0) Minimal Definitions: v2, tag, shortcut
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 2-adic valuation: largest t such that 2^t divides n. -/
def v2 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 0 then 1 + v2 (n / 2)
  else 0

/-- tag(n) = v2(3n + 1). -/
def tag (n : ℕ) : ℕ := v2 (3 * n + 1)

/-- shortcut(n) = (3n + 1) / 2^(tag(n)). -/
def shortcut (n : ℕ) : ℕ := (3 * n + 1) / (2 ^ (tag n))

-- ═══════════════════════════════════════════════════════════════════════════════
-- 1) R1-Pure: Window Certificate and Checker
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A specific Certificate format for a window of length L. -/
structure WindowCert (L : ℕ) where
  states : Fin (L + 1) → ℕ
  tags   : Fin L → ℕ

/-- The Validity Predicate (R1). -/
def IsValidWindow (L : ℕ) (c : WindowCert L) : Prop :=
  (∀ i : Fin L, c.tags i = tag (c.states (Fin.castSucc i))) ∧
  (∀ i : Fin L, c.states (Fin.succ i) = shortcut (c.states (Fin.castSucc i)))

/-- Sum of tags in a certificate (recursive on Nat). -/
def sumTagsAux (L : ℕ) (tags : Fin L → ℕ) (i : ℕ) (acc : ℕ) : ℕ :=
  if h : i < L then sumTagsAux L tags (i + 1) (acc + tags ⟨i, h⟩)
  else acc

def sumTags {L : ℕ} (tags : Fin L → ℕ) : ℕ := sumTagsAux L tags 0 0

/-- Window Property: There exists a valid certificate. -/
def Window (L : ℕ) (n : ℕ) (g : ℕ) (m : ℕ) : Prop :=
  ∃ c : WindowCert L,
    IsValidWindow L c ∧
    c.states 0 = n ∧
    c.states (Fin.last L) = m ∧
    (sumTags c.tags) = g

-- ═══════════════════════════════════════════════════════════════════════════════
-- 2) The Contraction Lemma
-- ═══════════════════════════════════════════════════════════════════════════════

-- 3 * n + 1 ≤ 4 * n
-- Proof: 3n + 1 ≤ 3n + n = 4n (since 1 ≤ n)
theorem local_bound (n : ℕ) (hn : n ≥ 1) : 3 * n + 1 ≤ 4 * n := by
  have h : 3 * n + n = 4 * n := by simp [Nat.succ_mul]
  rw [← h]
  exact Nat.add_le_add_left hn (3 * n)

theorem step_bound (n t : ℕ) (hn : n ≥ 1) :
    (3 * n + 1) / 2^t ≤ 4 * n / 2^t :=
  Nat.div_le_div_right (local_bound n hn)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 3) Game Positions and Turn (Local, No Import)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Game Position Types -/
inductive Pos
  | Root
  | Ask (n : ℕ)
  | Step (n : ℕ)
  | ProvideWin (L : ℕ) (n : ℕ) (g : ℕ) (m : ℕ)

/-- Turn indicator. -/
inductive Turn
  | P  -- Proponent
  | O  -- Opponent

/-- Turn function -/
def turnFn (p : Pos) : Turn :=
  match p with
  | Pos.Root => Turn.O
  | _        => Turn.P

-- ═══════════════════════════════════════════════════════════════════════════════
-- 4) Move Predicates (Pure Predicates, No Sets)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- P can move from p to q. -/
def pCanMove (p q : Pos) : Prop :=
  match p with
  | Pos.Ask n => q = Pos.Step n
  | Pos.Step n =>
      q = Pos.Ask (shortcut n) ∨
      ∃ L g m, q = Pos.ProvideWin L n g m
  | Pos.ProvideWin _ _ _ m => q = Pos.Ask m
  | Pos.Root => False

/-- O can move from p to q. -/
def oCanMove (p q : Pos) : Prop :=
  match p with
  | Pos.Root => ∃ n, q = Pos.Ask n
  | _ => False

/-- Generic move predicate. -/
def canMove (p q : Pos) : Prop :=
  match turnFn p with
  | Turn.P => pCanMove p q
  | Turn.O => oCanMove p q

/-- Position has at least one move. -/
def hasMoves (p : Pos) : Prop := ∃ q, canMove p q

-- ═══════════════════════════════════════════════════════════════════════════════
-- 5) Base and Good Predicates (Pure Predicates, No Sets)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Base predicate (parameterized by a predicate on ℕ). -/
def isBase (B : ℕ → Prop) (p : Pos) : Prop :=
  match p with
  | Pos.Ask n => B n
  | _ => False

/-- Good predicate (certified window with high gain). -/
def isGood (p : Pos) : Prop :=
  match p with
  | Pos.ProvideWin L n g m => Window L n g m ∧ g ≥ 2 * L + 1
  | _ => False

/-- Success predicate. -/
def isSuccess (B : ℕ → Prop) (p : Pos) : Prop :=
  isBase B p ∨ isGood p

-- ═══════════════════════════════════════════════════════════════════════════════
-- 6) Structural Closure (Local, Predicate-Based)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Up2-closed predicate: a predicate S is closed if it satisfies the Up2 rules. -/
def Up2Closed (B : ℕ → Prop) (S : Pos → Prop) : Prop :=
  (∀ p, isSuccess B p → S p) ∧
  (∀ p, turnFn p = Turn.P → (∃ q, pCanMove p q ∧ S q) → S p) ∧
  (∀ p, turnFn p = Turn.O → hasMoves p → (∀ q, oCanMove p q → S q) → S p)

/-- Up2Mem: the least closed predicate (intersection of all closed predicates). -/
def Up2Mem (B : ℕ → Prop) (p : Pos) : Prop :=
  ∀ S : Pos → Prop, Up2Closed B S → S p

/-- Avoid2 step predicate: p can stay in X without hitting Success. -/
def AvoidStep (B : ℕ → Prop) (X : Pos → Prop) (p : Pos) : Prop :=
  ¬ isSuccess B p ∧
  (turnFn p = Turn.P → ∀ q, pCanMove p q → X q) ∧
  (turnFn p = Turn.O → hasMoves p → ∃ q, oCanMove p q ∧ X q)

/-- Avoid2Closed: a predicate X is avoid-closed if AvoidStep X ⊆ X. -/
def Avoid2Closed (B : ℕ → Prop) (X : Pos → Prop) : Prop :=
  ∀ p, AvoidStep B X p → X p

/-- Avoid2Mem: the largest avoid-closed predicate (union of all avoid-closed predicates). -/
def Avoid2Mem (B : ℕ → Prop) (p : Pos) : Prop :=
  ∃ X : Pos → Prop, Avoid2Closed B X ∧ X p

-- ═══════════════════════════════════════════════════════════════════════════════
-- 7) Queue Definition
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The Queue (Structural Obstruction). -/
def Queue (B : ℕ → Prop) (p : Pos) : Prop := Avoid2Mem B p

/-- QueueGain: numbers in Ask that are in Queue with low gain. -/
def QueueGain (B : ℕ → Prop) (L : ℕ) (n : ℕ) : Prop :=
  Queue B (Pos.Ask n) ∧ ∀ g m, Window L n g m → g < 2 * L + 1

end RevHalt.Up2Gain

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom Checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms RevHalt.Up2Gain.v2
#print axioms RevHalt.Up2Gain.tag
#print axioms RevHalt.Up2Gain.shortcut
#print axioms RevHalt.Up2Gain.IsValidWindow
#print axioms RevHalt.Up2Gain.sumTagsAux
#print axioms RevHalt.Up2Gain.sumTags
#print axioms RevHalt.Up2Gain.Window
#print axioms RevHalt.Up2Gain.local_bound
#print axioms RevHalt.Up2Gain.step_bound
#print axioms RevHalt.Up2Gain.turnFn
#print axioms RevHalt.Up2Gain.pCanMove
#print axioms RevHalt.Up2Gain.oCanMove
#print axioms RevHalt.Up2Gain.canMove
#print axioms RevHalt.Up2Gain.hasMoves
#print axioms RevHalt.Up2Gain.isBase
#print axioms RevHalt.Up2Gain.isGood
#print axioms RevHalt.Up2Gain.isSuccess
#print axioms RevHalt.Up2Gain.Up2Closed
#print axioms RevHalt.Up2Gain.Up2Mem
#print axioms RevHalt.Up2Gain.AvoidStep
#print axioms RevHalt.Up2Gain.Avoid2Closed
#print axioms RevHalt.Up2Gain.Avoid2Mem
#print axioms RevHalt.Up2Gain.Queue
#print axioms RevHalt.Up2Gain.QueueGain
