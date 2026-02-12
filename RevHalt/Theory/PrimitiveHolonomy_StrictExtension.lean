import RevHalt.Theory.PrimitiveHolonomy

/-!
# Primitive Holonomy: Strict Extension over Set

Formal verification that Primitive Holonomy strictly extends classical (functional) theory.

Two decisive theorems:
1. **Separation**: In `Set` (functional semantics), `LagEvent` is impossible.
   This proves that `Lag` is a phenomenon strictly belonging to `Rel`.
2. **Recovery**: Restricting to `Set` recovers standard Holonomy (e.g., Monodromy).

Strictly constructive (no `noncomputable`, no `classical`).
-/

namespace PrimitiveHolonomy

variable {P : Type} [HistoryGraph P]
variable {S : Type} {V : Type}

/-!
## Theorem 1: The Impossibility of Lag in Set

If the semantics is functional (total and deterministic), then `Compatible` is always true
(because the function always maps to *something*).
Therefore, `LagEvent` (which requires `¬ Compatible` for one branch) is impossible.
-/

/-- A semantics is functional if every step relates each starting state *in the fiber* to exactly one ending state. -/
def FunctionalSemOnFiber
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∀ {h k : P} (p : HistoryGraph.Path h k) (x : FiberPt (P := P) obs target_obs h),
    ∃! y, sem.sem p x.1 y

/--
Theorem: In a functional semantics, `Compatible` is universally true for any valid fiber point.
-/
theorem compatible_of_functional
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (hFunc : FunctionalSemOnFiber sem obs target_obs)
    -- We need "Fiber Preserving" to ensure the functional result lands in the target fiber.
    (hFibPres : ∀ {h k} (p : HistoryGraph.Path h k) (x : S),
      obs x = target_obs h →
      ∀ y, sem.sem p x y → obs y = target_obs k)
    {h k : P} (p : HistoryGraph.Path h k)
    (x : FiberPt (P := P) obs target_obs h) :
    Compatible (P := P) sem obs target_obs p x :=
by
  -- Unpack functional property
  rcases hFunc p x with ⟨y, hsem, _⟩
  -- Prove y is in the target fiber
  have hy_in_fiber : obs y = target_obs k := hFibPres p x.1 x.2 y hsem
  -- Construct the witness in FiberPt
  let y_pt : FiberPt (P := P) obs target_obs k := ⟨y, hy_in_fiber⟩
  -- Prove compatibility
  refine ⟨y_pt, ?_⟩
  exact hsem


/--
**Main Theorem 1**: `LagEvent` is impossible in functional semantics (with fiber preservation).
-/
theorem no_LagEvent_of_Functional
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (hFunc : FunctionalSemOnFiber sem obs target_obs)
    (hFibPres : ∀ {h k} (p : HistoryGraph.Path h k) (x : S),
      obs x = target_obs h → ∀ y, sem.sem p x y → obs y = target_obs k)
    {h k k' : P} {p q : HistoryGraph.Path h k} (α : HistoryGraph.Deformation p q)
    (step : HistoryGraph.Path h k') :
    ¬ LagEvent (P := P) sem obs target_obs α step :=
by
  intro hLag
  rcases hLag with ⟨x, x', _hxne, _hHol, _hCompatX, hNotCompatX'⟩
  -- The contradiction is immediate: x' MUST be compatible in a functional semantics
  apply hNotCompatX'
  exact compatible_of_functional sem obs target_obs hFunc hFibPres step x'

/-!
## Theorem 2: Classical Recovery (Double Cover of S1)

We construct a concrete example:
- P = Bool (2 points: false, true).
- We simulate S1 by identifying positions modulo 2.
- Edges: `false -> true` and `true -> false`.
- S = Bool (Fiber is 2 points).
- Semantics: `false -> true` is Identity, `true -> false` is Swap.
- We show that for a "loop" (Path false false = composition of steps),
  the holonomy matches the classical permutation (Swap).
-/

inductive BoolPath : Bool → Bool → Type
| id (b : Bool) : BoolPath b b
| stepFT : BoolPath false true
| stepTF : BoolPath true false
| comp {a b c : Bool} : BoolPath a b → BoolPath b c → BoolPath a c

-- Trivial deformation relation
def BoolDef : ∀ {h k}, BoolPath h k → BoolPath h k → Prop := fun _ _ => False

instance BoolHG : HistoryGraph Bool where
  Path := BoolPath
  Deformation := BoolDef
  idPath := BoolPath.id
  compPath := BoolPath.comp

-- The space S is Bool x Bool (Base x Fiber)
-- obs returns the Base part.
def Base : Type := Bool
def Layer : Type := Bool
def Space : Type := Base × Layer

def obs (s : Space) : Base := s.1
def target_obs (b : Base) : Base := b

-- Semantics:
-- stepFT (false -> true): (false, L) -> (true, L)   (Identity Lift)
-- stepTF (true -> false): (true, L) -> (false, !L)  (Twisted Lift)

def boolRel : {h k : Base} → BoolPath h k → Space → Space → Prop
| _, _, BoolPath.id _ => fun s1 s2 => s1 = s2
| _, _, BoolPath.stepFT => fun s1 s2 =>
    s1.1 = false ∧ s2.1 = true ∧ s2.2 = s1.2 -- Identity on Layer
| _, _, BoolPath.stepTF => fun s1 s2 =>
    s1.1 = true ∧ s2.1 = false ∧ s2.2 = !s1.2 -- Negation on Layer
| _, _, BoolPath.comp p q => fun x z => ∃ y, boolRel p x y ∧ boolRel q y z

-- Semantics instance
-- We need a HistoryGraph instance for Base first.
instance BaseHG : HistoryGraph Base where
  Path := BoolPath
  Deformation := BoolDef
  idPath := BoolPath.id
  compPath := BoolPath.comp

def BoolSem : Semantics Base Space where
  sem := boolRel
  sem_id := by
    intro h x y
    cases h <;> { simp [boolRel]; rfl }
  sem_comp := by
    intro h k l p q x z
    simp [boolRel]
    rfl

-- Define the Loop: false -> true -> false
def Loop : BoolPath false false := BoolPath.comp BoolPath.stepFT BoolPath.stepTF

/--
**Main Theorem 2**: Classical Monodromy Recovery.
The primitive transport of the loop on the double cover is exactly the permutation (Swap).
Start at (false, false), go to (true, false), come back to (false, true).
-/
theorem DoubleCover_Recovery_Swap_False :
    Transport (P := Base) BoolSem obs target_obs Loop
      ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ :=
  Exists.intro (true, false) (
    And.intro
      (And.intro rfl (And.intro rfl rfl))
      (And.intro rfl (And.intro rfl rfl))
  )

theorem DoubleCover_Recovery_Swap_True :
    Transport (P := Base) BoolSem obs target_obs Loop
      ⟨(false, true), rfl⟩ ⟨(false, false), rfl⟩ :=
  Exists.intro (true, true) (
    And.intro
      (And.intro rfl (And.intro rfl rfl))
      (And.intro rfl (And.intro rfl rfl))
  )

-- Lemma: The semantics preserves the fiber structure (explicitly for BoolSem)
theorem boolSem_preserves_fiber {h k : Base} (p : BoolPath h k) :
    ∀ (s : Space), obs s = h → ∀ (y : Space), BoolSem.sem p s y → obs y = k := by
  induction p with
  | id =>
    intro s hs y hrel
    simp [BoolSem, boolRel] at hrel
    rw [← hrel, hs]
  | stepFT =>
    intro s hs y hrel
    simp [BoolSem, boolRel] at hrel
    change y.1 = true
    rw [hrel.2.1]
  | stepTF =>
    intro s hs y hrel
    simp [BoolSem, boolRel] at hrel
    change y.1 = false
    rw [hrel.2.1]
  | comp p q ihp ihq =>
    intro s hs y hrel
    rcases hrel with ⟨z, hz1, hz2⟩
    have hz_obs : obs z = _ := ihp s hs z hz1
    exact ihq z hz_obs y hz2

-- Add functional proof to complete the picture
-- We define FunctionalSemOnFiber for this specific semantics
theorem functional_BoolSem : FunctionalSemOnFiber (P := Base) BoolSem obs target_obs := by
  intro h k p x
  induction p with
  | id =>
    refine ⟨x.1, ?_, ?_⟩
    · simp [BoolSem, boolRel]
    · intro y hy
      simp [BoolSem, boolRel] at hy
      exact hy.symm
  | stepFT =>
    refine ⟨(true, x.1.2), ?_, ?_⟩
    · have hx : x.1.1 = false := x.2
      simp [BoolSem, boolRel, hx]
    · intro y hy
      simp [BoolSem, boolRel] at hy
      rcases hy with ⟨_, hy2, hy3⟩
      apply Prod.ext
      · exact hy2
      · exact hy3
  | stepTF =>
    refine ⟨(false, !x.1.2), ?_, ?_⟩
    · have hx : x.1.1 = true := x.2
      simp [BoolSem, boolRel, hx]
    · intro y hy
      simp [BoolSem, boolRel] at hy
      rcases hy with ⟨_, hy2, hy3⟩
      apply Prod.ext
      · exact hy2
      · exact hy3
  | comp p q ih_p ih_q =>
    rcases ih_p x with ⟨y, hy_sem, hy_unique⟩
    have hy_in_fiber : obs y = _ := boolSem_preserves_fiber p x.1 x.2 y hy_sem
    let y_fib : FiberPt obs target_obs _ := ⟨y, hy_in_fiber⟩
    rcases ih_q y_fib with ⟨z, hz_sem, hz_unique⟩
    refine ⟨z, ?_, ?_⟩
    · exact ⟨y, hy_sem, hz_sem⟩
    · intro z' hz'
      rcases hz' with ⟨y', hy'p, hy'q⟩
      have hy_eq : y' = y := hy_unique y' hy'p
      rw [hy_eq] at hy'q
      exact hz_unique z' hy'q

#print axioms no_LagEvent_of_Functional
#print axioms DoubleCover_Recovery_Swap_False
#print axioms DoubleCover_Recovery_Swap_True
