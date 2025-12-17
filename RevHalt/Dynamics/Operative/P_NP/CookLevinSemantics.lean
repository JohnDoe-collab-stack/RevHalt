/-
  RevHalt.Dynamics.Operative.P_NP.CookLevinSemantics

  Stage B: Machine execution semantics for tableau encoding.
  Provides abstract execution model independent of SAT/LR.
-/
import RevHalt.Dynamics.Operative.P_NP.CookLevinTableau
import RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas

namespace RevHalt.Dynamics.Operative.P_NP.CookLevinSemantics

open RevHalt.Dynamics.Operative.P_NP.CookLevinTableau
open RevHalt.Dynamics.Operative.P_NP.CookLevinLemmas

/-! ## Configuration and Step Relation -/

/-- Configuration at time t. Bounds (k < S, q < numStates) are imposed elsewhere. -/
structure Cfg where
  q    : ℕ          -- Current state
  hd   : ℕ          -- Head position
  tape : ℕ → ℕ      -- Tape contents (total function, bounds imposed separately)

/-- One-step transition relation according to machine rules + inertia. -/
def StepCfg (S : ℕ) (M : TableauMachine) (c c' : Cfg) : Prop :=
  ∃ (rIdx : ℕ) (hrIdx : rIdx < M.rules.length),
    let r := M.rules.get ⟨rIdx, hrIdx⟩
    -- Pre-condition: current state and symbol under head match rule
    c.q = r.q ∧ c.tape c.hd = r.s ∧
    -- Post-condition: next state, symbol write, head move
    c'.q = r.q' ∧
    c'.hd = movePos r.mv c.hd ∧
    c'.tape c.hd = r.s' ∧
    -- Inertia: all other cells unchanged
    (∀ k < S, k ≠ c.hd → c'.tape k = c.tape k)

/-- Deterministic step: given (q, symbol), there's exactly one applicable rule. -/
def Deterministic (M : TableauMachine) : Prop :=
  ∀ r₁ r₂ : TransitionRule, r₁ ∈ M.rules → r₂ ∈ M.rules →
    r₁.q = r₂.q → r₁.s = r₂.s → r₁ = r₂

/-! ## Bounded Execution -/

/--
Bounded execution up to T steps.
Init: starts at (q0, head0, tape0).
Steps: each step follows StepCfg.
Accept: reaches qAcc at some t ≤ T.
-/
structure ExecUpTo (T S : ℕ) (M : TableauMachine) (q0 head0 qAcc : ℕ) (tape0 : ℕ → ℕ) where
  cfg     : ℕ → Cfg
  init_q  : (cfg 0).q = q0
  init_hd : (cfg 0).hd = head0
  init_tp : ∀ k < S, (cfg 0).tape k = tape0 k
  step    : ∀ t, t < T → StepCfg S M (cfg t) (cfg (t+1))
  accept  : ∃ t ≤ T, (cfg t).q = qAcc

/-- Configuration bounds are preserved by StepCfg. -/
theorem stepCfg_preserves_bounds
    {S : ℕ} {M : TableauMachine} {c c' : Cfg}
    (hStep : StepCfg S M c c')
    (hq : c.q < M.numStates) (hhd : c.hd < S)
    (htp : ∀ k < S, c.tape k < M.numSymbols) :
    c'.q < M.numStates ∧ c'.hd < S ∧ (∀ k < S, c'.tape k < M.numSymbols) := by
  sorry

/-! ## Conversion from TableauRun to ExecUpTo -/

/-- Convert a TableauRun to a configuration sequence. -/
def cfgOfRun (R : TableauRun) : ℕ → Cfg :=
  fun t => { q := R.st t, hd := R.hd t, tape := R.tape t }

/-- ValidRun induces an ExecUpTo (as a definition since ExecUpTo is a structure). -/
noncomputable def validRun_to_exec
    (T S : ℕ) (M : TableauMachine)
    (q0 head0 qAcc : ℕ) (tape0 : ℕ → ℕ)
    (witLen witOff sym0 sym1 : ℕ)
    {R : TableauRun}
    (hR : ValidRun T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1 R) :
    ExecUpTo T S M q0 head0 qAcc
      (fun k => if k >= witOff ∧ k < witOff + witLen then
                  if R.wit (k - witOff) then sym1 else sym0
                else tape0 k) := by
  sorry

/-- ExecUpTo induces a ValidRun (with same witness). -/
theorem exec_to_validRun
    (T S : ℕ) (M : TableauMachine)
    (q0 head0 qAcc : ℕ) (tape0 : ℕ → ℕ)
    (witLen witOff sym0 sym1 : ℕ)
    (wit : ℕ → Bool)
    (E : ExecUpTo T S M q0 head0 qAcc
      (fun k => if k >= witOff ∧ k < witOff + witLen then
                  if wit (k - witOff) then sym1 else sym0
                else tape0 k)) :
    ∃ R : TableauRun, ValidRun T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1 R ∧
      R.wit = wit := by
  sorry

/-! ## Main Stage B Theorem -/

/--
ValidRun ⟺ ExecUpTo (modulo witness extraction).
This is the key Stage B result: tableau semantics = execution semantics.
-/
theorem validRun_iff_exec_exists_wit
    (T S : ℕ) (M : TableauMachine)
    (q0 head0 qAcc : ℕ) (tape0 : ℕ → ℕ)
    (witLen witOff sym0 sym1 : ℕ) :
    (∃ R : TableauRun, ValidRun T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1 R) ↔
    (∃ wit : ℕ → Bool,
      Nonempty (ExecUpTo T S M q0 head0 qAcc
        (fun k => if k >= witOff ∧ k < witOff + witLen then
                    if wit (k - witOff) then sym1 else sym0
                  else tape0 k))) := by
  constructor
  · intro ⟨R, hR⟩
    exact ⟨R.wit, ⟨validRun_to_exec T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1 hR⟩⟩
  · intro ⟨wit, ⟨E⟩⟩
    obtain ⟨R, hR, _⟩ := exec_to_validRun T S M q0 head0 qAcc tape0 witLen witOff sym0 sym1 wit E
    exact ⟨R, hR⟩

end RevHalt.Dynamics.Operative.P_NP.CookLevinSemantics
