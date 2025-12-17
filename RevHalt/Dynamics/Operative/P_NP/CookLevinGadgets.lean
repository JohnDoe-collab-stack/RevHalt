/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets

  Small CNF gadget library used by Cook–Levin encodings:
  - variable naming via Nat.pair
  - literals / clauses
  - atLeastOne / atMostOne / exactlyOne
-/

import RevHalt.Dynamics.Operative.P_NP.SAT
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.Basic

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF

/-- Local aliases (match your SAT.lean conventions). -/
abbrev Var    := CNF.Var
abbrev Lit    := CNF.Lit
abbrev Clause := CNF.Clause
abbrev Formula := CNF.CNF

/-- Positive literal. -/
def pos (v : Var) : Lit := ⟨v, false⟩

/-- Negative literal. -/
def neg (v : Var) : Lit := ⟨v, true⟩

/-- Single-literal clause. -/
def unit (ℓ : Lit) : Clause := [ℓ]

/-- Conjunction of CNFs is list append. -/
def andCNF (F G : Formula) : Formula := F ++ G

/-- Big conjunction of many CNFs. -/
def andCNFs (Fs : List Formula) : Formula := Fs.flatten

/--
A simple, injective variable naming scheme.
`tag` distinguishes families (state/head/tape/etc.),
the rest are indices (time/cell/symbol/...) packed with Nat.pair.
-/
def mkVar (tag a b c : ℕ) : Var :=
  Nat.pair tag (Nat.pair a (Nat.pair b c))

/-- At-least-one constraint: (v₁ ∨ ... ∨ vₙ). Empty = unsat CNF (we leave it as `[]` and handle upstream). -/
def atLeastOne (vs : List Var) : Formula :=
  match vs with
  | [] => []      -- convention: caller avoids [] if it wants a real constraint
  | _  => [vs.map pos]

/-- Helper: all unordered pairs (i<j) from a list. -/
def pairwise {α : Type} : List α → List (α × α)
  | []      => []
  | x :: xs => (xs.map (fun y => (x, y))) ++ pairwise xs

/-- At-most-one constraint: for all i<j, (¬vᵢ ∨ ¬vⱼ). -/
def atMostOne (vs : List Var) : Formula :=
  (pairwise vs).map (fun p => [neg p.1, neg p.2])

/-- Exactly-one = atLeastOne ∧ atMostOne. -/
def exactlyOne (vs : List Var) : Formula :=
  andCNF (atLeastOne vs) (atMostOne vs)

end RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets
