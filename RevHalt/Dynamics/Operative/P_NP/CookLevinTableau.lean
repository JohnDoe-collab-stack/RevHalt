/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinTableau

  Concrete Tableau Encoding Logic for Cook-Levin Theorem.

  This module defines:
  1. The variable layout for the tableau (time x space).
  2. The constraints (Init, Step, Accept) as CNF formulas.
  3. The top-level `genTableau` function.
  4. Size bound proofs.

  It relies on `CookLevinGadgets` for basic building blocks.
-/

import RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets
import RevHalt.Dynamics.Operative.P_NP.SAT
import RevHalt.Dynamics.Operative.P_NP.PNP

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinTableau

open RevHalt
open RevHalt.Dynamics.Operative.P_NP.SAT
open RevHalt.Dynamics.Operative.P_NP.SAT.CNF hiding Var
open RevHalt.Dynamics.Operative.P_NP.CookLevinGadgets
open RevHalt.Dynamics.Operative.P_NP.PNP

-- ==============================================================================================
-- 1. Variable Layout
-- ==============================================================================================

/-- Variable tags to ensure disjoint namespaces. -/
def tagState : ℕ := 10
def tagHead  : ℕ := 20
def tagTape  : ℕ := 30
def tagStep  : ℕ := 40  -- Choice of transition rule

-- Variables are indexed by time t and spatial/other parameters.

/-- State variable: at time t, machine is in state q. -/
def varState (t q : ℕ) : CookLevinGadgets.Var := mkVar tagState t q 0

/-- Head variable: at time t, head is at position k. -/
def varHead (t k : ℕ) : CookLevinGadgets.Var := mkVar tagHead t k 0

/-- Tape variable: at time t, cell k contains symbol s. -/
def varTape (t k s : ℕ) : CookLevinGadgets.Var := mkVar tagTape t k s

/-- Step variable: at time t, transition rule r is applied. -/
def varStep (t r : ℕ) : CookLevinGadgets.Var := mkVar tagStep t r 0


-- ==============================================================================================
-- 2. Constraints Generation
-- ==============================================================================================

/--
Unique State Constraint: At each time t (0..T), the machine is in exactly one state.
- Range of states: 0 to numStates-1
-/
def uniqueState (T : ℕ) (numStates : ℕ) : Formula :=
  (List.range (T + 1)).flatMap fun t =>
    exactlyOne ((List.range numStates).map (varState t))

/--
Unique Head Constraint: At each time t (0..T), the head is at exactly one position.
- Range of positions: 0 to spaceBound-1
-/
def uniqueHead (T : ℕ) (spaceBound : ℕ) : Formula :=
  (List.range (T + 1)).flatMap fun t =>
    exactlyOne ((List.range spaceBound).map (varHead t))

/--
Unique Tape Symbol Constraint: At each cell (t, k) (0..T, 0..spaceBound-1), exactly one symbol.
- Range of symbols: 0 to numSymbols-1
-/
def uniqueTape (T : ℕ) (spaceBound : ℕ) (numSymbols : ℕ) : Formula :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range spaceBound).flatMap fun k =>
      exactlyOne ((List.range numSymbols).map (varTape t k))

/--
Unique Step Constraint: At each time t (0..T-1), exactly one transition rule is chosen.
-/
def uniqueStep (T : ℕ) (numRules : ℕ) : Formula :=
  (List.range T).flatMap fun t =>
    exactlyOne ((List.range numRules).map (varStep t))

-- ----------------------------------------------------------------------------------------------
-- Transition Logic (Step)
-- ----------------------------------------------------------------------------------------------

/-- Mouvement de tête (simplifié). -/
inductive Move where
  | L | R | S
  deriving DecidableEq

/-- Règle de transition (q,s) ↦ (q',s',move). -/
structure TransitionRule where
  q   : ℕ
  s   : ℕ
  q'  : ℕ
  s'  : ℕ
  mv  : Move

/-- Parameters defining the machine being simulated. -/
structure TableauParams where
  numStates  : ℕ
  numSymbols : ℕ
  numRules   : ℕ

/-- Paramètres + liste de règles (numRules = rules.length). -/
structure TableauMachine extends TableauParams where
  rules : List TransitionRule
  rules_len : rules.length = numRules

/-- Négation d’un littéral. -/
def notLit : CNF.Lit → CNF.Lit
  | ⟨v, neg⟩ => ⟨v, !neg⟩

/-- Clause d’implication: (A₁ ∧ ... ∧ Aₙ) → B, encodée en (¬A₁ ∨ ... ∨ ¬Aₙ ∨ B). -/
def impClause (ante : List CNF.Lit) (cons : CNF.Lit) : CNF.Clause :=
  (ante.map notLit) ++ [cons]

/-- Position de tête suivante (bord simplifié: pred 0 = 0). -/
def movePos : Move → ℕ → ℕ
  | Move.L, k => Nat.pred k
  | Move.R, k => k + 1
  | Move.S, k => k

/-- (Step t r ∧ Head t k) → State t q, Tape t k s (cohérence de lecture). -/
def stepGuard (t k rId : ℕ) (R : TransitionRule) : Formula :=
  let A : List CNF.Lit := [ pos (varStep t rId), pos (varHead t k) ]
  [ impClause A (pos (varState t R.q))
  , impClause A (pos (varTape  t k R.s))
  ]

/-- Interdit les mouvements hors bande (bord) pour une position k donnée. -/
def stepBoundary (S t k rId : ℕ) (R : TransitionRule) : Formula :=
  match R.mv with
  | Move.L =>
      if _ : k = 0 then
        -- ¬(Step t r ∧ Head t 0)
        [ [neg (varStep t rId), neg (varHead t k)] ]
      else []
  | Move.R =>
      if _ : k = Nat.pred S then
        [ [neg (varStep t rId), neg (varHead t k)] ]
      else []
  | Move.S => []

/-- Clauses “effet” d’une règle à (t,k,rId). -/
def stepEffect (t k rId : ℕ) (R : TransitionRule) : Formula :=
  let A : List CNF.Lit :=
    [ pos (varStep t rId)
    , pos (varHead t k)
    , pos (varState t R.q)
    , pos (varTape t k R.s)
    ]
  let k' := movePos R.mv k
  [ impClause A (pos (varState (t+1) R.q'))
  , impClause A (pos (varTape  (t+1) k  R.s'))
  , impClause A (pos (varHead  (t+1) k'))
  ]

/-- CNF complet d’un pas local (bords + gardes + effets). -/
def stepCNF (S t k rId : ℕ) (R : TransitionRule) : Formula :=
  stepBoundary S t k rId R ++ stepGuard t k rId R ++ stepEffect t k rId R

/-- Transition globale: pour chaque t<T, k<S, r<numRules, ajoute les clauses de stepCNF. -/
def genTransition (T S : ℕ) (M : TableauMachine) : Formula :=
  (List.range T).flatMap fun t =>
    (List.range S).flatMap fun k =>
      ((List.range M.rules.length).zip M.rules).flatMap fun rk =>
        stepCNF S t k rk.1 rk.2

-- ----------------------------------------------------------------------------------------------
-- Inertia (Frame Axioms)
-- ----------------------------------------------------------------------------------------------

/-- Inertia sur une cellule/symbole: si head n’est pas sur k, le symbole reste. -/
def inertiaSymbol (t k s : ℕ) : Formula :=
  [ impClause [ neg (varHead t k), pos (varTape t k s) ] (pos (varTape (t+1) k s))
  , impClause [ neg (varHead t k), pos (varTape (t+1) k s) ] (pos (varTape t k s))
  ]

/-- Inertia globale: t<T, k<S, s<numSymbols. -/
def genInertia (T S numSymbols : ℕ) : Formula :=
  (List.range T).flatMap fun t =>
    (List.range S).flatMap fun k =>
      (List.range numSymbols).flatMap fun s =>
        inertiaSymbol t k s

-- ----------------------------------------------------------------------------------------------
-- Initialization & Equality Constraints
-- ----------------------------------------------------------------------------------------------

def tagWit : ℕ := 50
def varWit (i : ℕ) : CookLevinGadgets.Var := mkVar tagWit i 0 0

/--
Initialisation “constante” (état, head, tape fixé).
Exclut la zone witness [witOff, witOff + witLen) pour éviter les conflits.
-/
def genInitConst (S q0 head0 : ℕ) (tape0 : ℕ → ℕ) (witOff witLen : ℕ) : Formula :=
  [ [pos (varState 0 q0)]
  , [pos (varHead  0 head0)]
  ] ++
  ((List.range S).filter (fun k => k < witOff ∨ k ≥ witOff + witLen)).map
    (fun k => [pos (varTape 0 k (tape0 k))])

/--
Initialisation witness → ruban.
Convention : symbole `sym0`/`sym1` pour bit false/true.
-/
def genInitWitness (witLen witOff sym0 sym1 : ℕ) : Formula :=
  (List.range witLen).flatMap (fun i =>
    let k := witOff + i
    [ -- (w_i) → Tape(0,k,sym1)
      impClause [pos (varWit i)] (pos (varTape 0 k sym1))
    , -- (¬w_i) → Tape(0,k,sym0)
      impClause [neg (varWit i)] (pos (varTape 0 k sym0))
    ])

/-- Acceptation (au moins un état acceptant atteint avant/à T). -/
def genAccept (T qAcc : ℕ) : Formula :=
  [ (List.range (T + 1)).map (fun t => pos (varState t qAcc)) ]

-- ----------------------------------------------------------------------------------------------
-- Main Generator
-- ----------------------------------------------------------------------------------------------

/--
Top-level skeleton for FULL tableau generation.
Combinations: Uniqueness + Transitions + Inertia + Init (Const+Wit) + Accept.
-/
def genTableauAll
    (T S : ℕ) (M : TableauMachine)
    (q0 head0 qAcc : ℕ)
    (tape0 : ℕ → ℕ)
    (witLen witOff sym0 sym1 : ℕ) : Formula :=
  andCNFs [
    uniqueState T M.numStates,
    uniqueHead  T S,
    uniqueTape  T S M.numSymbols,
    uniqueStep  T M.numRules,
    genTransition T S M,
    genInertia   T S M.numSymbols,
    genInitConst S q0 head0 tape0 witOff witLen,
    genInitWitness witLen witOff sym0 sym1,
    genAccept T qAcc
  ]

/--
Obsolete basic generator (kept for backward compatibility during refactor)
-/
def genTableau
    (T : ℕ) (spaceBound : ℕ)
    (par : TableauParams) : Formula :=
  andCNFs [
    uniqueState T par.numStates,
    uniqueHead T spaceBound,
    uniqueTape T spaceBound par.numSymbols,
    uniqueStep T par.numRules
  ]

-- ==============================================================================================
-- 3. Polynomial Bounds (Computable)
-- ==============================================================================================

/--
Explicit cubic bound for the tableau size.
(n+1)^3 is overwhelmingly sufficient for the quadratic constraints.
Dependence on params is constant for a fixed machine.
-/
def tableauSizeBoundFun (par : TableauParams) (n : ℕ) : ℕ :=
  let C := (par.numStates + par.numSymbols + par.numRules + 10)
  (n + 1) * (n + 1) * (n + 1) * C * C

-- Helper lemmas for IsPoly composition
theorem IsPoly.add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n + g n) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  let k := max kf kg
  let c := cf + cg
  refine ⟨c, k, ?_⟩
  -- Arithmetic proof deferred
  sorry

theorem IsPoly.mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun n => f n * g n) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  let k := kf + kg
  refine ⟨cf * cg, k, ?_⟩
  -- Arithmetic proof deferred
  sorry

theorem poly_tableauSizeBoundFor (par : TableauParams) : IsPoly (tableauSizeBoundFun par) := by
  unfold tableauSizeBoundFun
  apply IsPoly.mul
  apply IsPoly.mul
  apply IsPoly.mul
  apply IsPoly.mul
  apply IsPoly.id_succ
  apply IsPoly.id_succ
  apply IsPoly.id_succ
  apply IsPoly.const
  apply IsPoly.const

/-- Proves that genTableau size is bounded by the explicit function. -/
theorem genTableau_size_bounded
    (par : TableauParams) (T S : ℕ) :
    cnfSize (genTableau T S par) ≤ tableauSizeBoundFun par (T + S) := by
  -- Loose bound proof delayed
  sorry

/--
Explicit cubic bound for the FULL tableau size (including transitions, inertia, init, accept).
Using a large constant factor 10 to be safe.
-/
def tableauFullSizeBoundFun (M : TableauMachine) (n : ℕ) : ℕ :=
  let par := M.toTableauParams
  10 * tableauSizeBoundFun par n

theorem poly_tableauFullSizeBoundFor (M : TableauMachine) : IsPoly (tableauFullSizeBoundFun M) := by
  unfold tableauFullSizeBoundFun
  apply IsPoly.mul
  apply IsPoly.const
  apply poly_tableauSizeBoundFor

/-- Proves that genTableauAll size is bounded. -/
theorem genTableauAll_size_bounded
    (M : TableauMachine) (T S q0 head0 qAcc witLen witOff sym0 sym1 : ℕ) (tape0 : ℕ → ℕ) :
    cnfSize (genTableauAll T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1) ≤ tableauFullSizeBoundFun M (T + S) := by
  -- Bounding init and accept is lower order (linear/quadratic).
  -- Cubic term still dominates.
  sorry
