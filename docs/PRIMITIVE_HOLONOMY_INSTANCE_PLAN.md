# PrimitiveHolonomy Instance Plan (Constructive, No Cheating)

Goal: add a new Lean file `RevHalt/Theory/PrimitiveHolonomy_instance.lean` that
imports `RevHalt.Theory.PrimitiveHolonomy` and provides a *concrete model* with
explicit witnesses (no `classical`, no `noncomputable`, no choice).

Non-goals:
- Do not copy/paste the whole theory file.
- Do not add any classical reasoning, choice, or quantifier-negation "swaps".
- Keep the instance minimal but non-trivial (at least one `TwistedHolonomy` and
  one `LagEvent` witness).

## 1. Skeleton

Create `RevHalt/Theory/PrimitiveHolonomy_instance.lean`:

- `import RevHalt.Theory.PrimitiveHolonomy`
- `namespace PrimitiveHolonomy` (reuse the same namespace as the theory file)

## 2. A Tiny HistoryGraph

Pick:
- `P := Unit`
- One hom-type with explicit parallel paths.

Define a path language where composition is *syntactic* so `sem_comp` can be `rfl`:

- `inductive ToyPath : Unit -> Unit -> Type`
  - `| id : ToyPath () ()`
  - `| p  : ToyPath () ()`       -- "interesting" path
  - `| q  : ToyPath () ()`       -- second path, used for holonomy
  - `| r  : ToyPath () ()`       -- third path, used to force non-factorization
  - `| step : ToyPath () ()`     -- used for compatibility / lag
  - `| comp : ToyPath () () -> ToyPath () () -> ToyPath () ()`

Define a deformation relation with *two* generating 2-cells (minimal for a real
`¬ FactorsHolonomy` witness):

- Option A (simplest): an inductive relation with two constructors:

  - `inductive ToyDef : {h k : Unit} -> ToyPath h k -> ToyPath h k -> Prop`
    - `| pq : ToyDef ToyPath.p ToyPath.q`
    - `| pr : ToyDef ToyPath.p ToyPath.r`

Then you get two explicit deformations:
- `α₁ : ToyDef ToyPath.p ToyPath.q := ToyDef.pq`
- `α₂ : ToyDef ToyPath.p ToyPath.r := ToyDef.pr`

Define the `HistoryGraph` instance:
- `Path := ToyPath`
- `Deformation := ToyDef`
- `idPath := ToyPath.id`
- `compPath := ToyPath.comp`

No category laws needed.

## 3. A Concrete State Space and Observables

Pick a state space with at least two points in the same fiber:
- Use the "product" shape already present in the theory file:
  - `Y := Unit`
  - `B := Bool`
  - `S := LagState Y B`
  - `V := Y`
  - `obs : S -> V := lagObs` (projects to `visible`)
  - `target_obs : P -> V := fun _ => ()`

Then every state is in every fiber, constructively (membership proof is `rfl`),
since `obs s = () = target_obs ()`.

Define two distinct fiber points:
- Let `s0 : S := ⟨(), false⟩` and `s1 : S := ⟨(), true⟩`.
- `x  : FiberPt obs target_obs () := ⟨s0, rfl⟩`
- `x' : FiberPt obs target_obs () := ⟨s1, rfl⟩`
- Prove `hx : x != x'` by `Subtype.ext` reducing to `false != true`.
- Also record `hHidden : x.1.hidden != x'.1.hidden` (again by `rfl`-reduction).

## 4. A Semantics With Definitional Composition

Define relations on `S := LagState Unit Bool`:
- `R_p : Relation S S := fun a b => a.hidden = false ∧ b.hidden = true ∧ b.visible = ()`
- `R_q : Relation S S := relId`  -- keep holonomy simple
- `R_r : Relation S S := fun _ _ => False`  -- empty relation, used to separate holonomies
- `R_step : Relation S S := fun a b => a.hidden = false ∧ b.hidden = false ∧ b.visible = ()`

Define `sem : ToyPath () () -> Relation S S` by recursion:
- `sem id       := relId`
- `sem p        := R_p`
- `sem q        := R_q`
- `sem r        := R_r`
- `sem step     := R_step`
- `sem (comp u v) := relComp (sem u) (sem v)`  -- definitional

Build `Semantics`:
- `sem_id` is `RelEq relId relId` (prove by `intro x y; exact Iff.rfl`).
- `sem_comp` is `RelEq (relComp (sem u) (sem v)) (relComp (sem u) (sem v))`
  (prove by `intro x y; exact Iff.rfl`).

This guarantees:
- No need for `funext`, `propext`, or rewriting tricks.
- `sem_comp` is "by definitional equality".

## 5. Witness: TwistedHolonomy

We want an explicit witness of
`TwistedHolonomy sem obs target_obs α` for `α : Deformation p q`.

Strategy:
- Use `x` and `x'` above.
- Show `HolonomyRel sem obs target_obs α x x'`.

Easiest proof path:
- Use the lemma `holonomy_def` (it is `rfl`) and provide a witness `y := x'`.
- Need:
  - `Transport sem obs target_obs ToyPath.p x y` holds because `R_p false true`.
  - `Transport sem obs target_obs ToyPath.q x' y` holds because `R_q` is `relId`,
    and `y = x'`.
- Conclude `x != x'` and get `TwistedHolonomy ...`.

## 6. Witness: LagEvent

We want an explicit witness of
`LagEvent sem obs target_obs α ToyPath.step`.

Preferred (more informative): use the theorem already in the file,
`lag_of_twist_and_hidden_step`, which factors the argument through
`StepDependsOnHidden`.

1. Prove `StepDependsOnHidden sem target_obs ToyPath.step`:
   - From `Compatible ... step x` you can extract a witness `y` and hence
     `x.1.hidden = false` (by the definition of `R_step`).
   - So if both `Compatible ... step x` and `Compatible ... step x'` hold, you get
     `x.1.hidden = false` and `x'.1.hidden = false`, hence `x.1.hidden = x'.1.hidden`,
     contradicting the hypothesis `x.1.hidden != x'.1.hidden`.

2. Apply `lag_of_twist_and_hidden_step` with:
   - the same `x`, `x'`, `hx`, and `hHol` from the twisted holonomy witness,
   - plus a single compatibility witness `Compatible ... step x` (pick `y := x`).

Alternative (still ok): use `lag_of_witness` directly by also proving
`¬ Compatible ... step x'` from `R_step` forcing `x'.1.hidden = false`.

This produces a clean, fully witnessed "lag" example.

## 7. Optional: Scheduling / Cofinal (Cheap Coverage)

Add a trivial scheduling (to exercise the "cofinal future" infrastructure):

- `toyScheduling : Scheduling (P := Unit) Nat` with:
  - `c := fun _ => ()`
  - `mono := fun _ => reach_refl ()`
  - `cofinal := fun _ => ⟨0, reach_refl ()⟩`

Then you can also test the "Along scheduling" layer:
- `CellsAlong toyScheduling`
- `AutoRegulatedAlong ... toyScheduling` / `ObstructionAlong ... toyScheduling`
- and the bridge lemmas to `AutoRegulatedCofinal` / `ObstructionCofinal`

## 8. Optional: Gauge / AutoRegulated / Obstruction (If Needed Later)

Add only what is actually checkable with the current definitions (no extra
assumptions about gauges).

Key observation (constructive, and important):
- A `Gauge` can be the empty relation. Since corrected transports are
  `Transport ∘ gauge`, an empty gauge makes every corrected holonomy empty.
  Therefore, the current `Obstruction` (twist-only, "for all gauges") is
  *very hard* to satisfy and often outright refutable.

What you can test cleanly in the instance file:

1. A vacuous positive case:
   - `AutoRegulated sem obs target_obs (∅)` holds (any gauge works, since there
     are no cells to check).

2. A non-vacuous negative case (shows why "holes" matter):
   - Let `c₁ : Cell (P := Unit) := ⟨(), (), ToyPath.p, ToyPath.q, ⟨ToyDef.pq⟩⟩`
     and `J₁ := Set.singleton c₁`.
   - Prove `¬ AutoRegulated sem obs target_obs J₁`:
     - For any gauge `φ`, `CorrectedTransport ... φ ToyPath.p` cannot relate any
       `x` whose `hidden = true`, because it is `Transport p` followed by a gauge,
       and `Transport p` itself has no outputs from such `x`.
     - Hence `CorrectedHolonomy ... φ α₁ xtrue xtrue` is `False` for
       `xtrue := ⟨⟨(), true⟩, rfl⟩`.
     - But `AutoRegulated` would force `CorrectedHolonomy ... ↔ xtrue = xtrue`,
       contradiction.

3. A clean refutation of `Obstruction` for any `J`:
   - Define `emptyGauge : Gauge obs target_obs := fun {_h _k} _p => fun _ _ => False`.
   - Show `CorrectedHolonomy sem obs target_obs emptyGauge α x x'` is always `False`.
   - Conclude `¬ Obstruction sem obs target_obs J` by instantiating the `∀ φ`
     in `Obstruction` with `emptyGauge` (no classical reasoning).

If later you want a positive "every gauge fails" notion, you likely need to
strengthen the gauge interface (e.g. require some reflexivity/non-emptiness),
or broaden obstruction to include diagonal holes (a "Defect" = hole or twist).

## 9. Real `¬ FactorsHolonomy` (Two Deformations, No Extra Assumptions)

With only one 2-cell, `FactorsHolonomy` is typically satisfiable by "hardcoding"
`H` on that single case. The two-deformation setup above is the minimal way to
get a *real* counterexample.

Concrete recipe (uses your existing lemma `witness_no_factor`):

1. Use the two deformations:
   - `α₁ : p ⇒ q` (constructor `ToyDef.pq`)
   - `α₂ : p ⇒ r` (constructor `ToyDef.pr`)

2. Use a trivial 1D summary with one code:
   - `Q := Unit`
   - `summ : Summary (P := Unit) Unit := fun {h k} _p => ()`

   Then the code equalities required by `witness_no_factor` are `rfl`.

3. Prove the holonomies differ (no classical; pick a witness pair):
   - Let `x := ⟨⟨(), false⟩, rfl⟩` and `x' := ⟨⟨(), true⟩, rfl⟩`.
   - Show `HolonomyRel sem obs target_obs α₁ x x'` holds
     (same proof as TwistedHolonomy: witness `y := x'` and `q` is `relId`).
   - Show `¬ HolonomyRel sem obs target_obs α₂ x x'` because
     the second leg uses `Transport ... r`, and `R_r` is the empty relation.

   This gives `¬ RelEq (HolonomyRel ... α₁) (HolonomyRel ... α₂)` by specializing
   the `RelEq` definition at `x x'`.

4. Apply:
   - `witness_no_factor sem obs target_obs summ (α₁ := α₁) (α₂ := α₂) rfl rfl hne`
   to obtain `¬ FactorsHolonomy sem obs target_obs summ`.

## 10. Cleanliness Checks

In the instance file (or a temporary check file you delete), add:
- `#print axioms` for the new `ToyHistoryGraph`, `ToySemantics`, and the witness
  lemmas (`example : TwistedHolonomy ...`, `example : LagEvent ...`).
  Also add one `example : ¬ FactorsHolonomy ...` (the construction above).
  Optionally add:
  - `example : AutoRegulated sem obs target_obs (∅)`
  - `example : ¬ AutoRegulated sem obs target_obs (Set.singleton c₁)`
  - `example : ¬ Obstruction sem obs target_obs (Set.singleton c₁)` (or any `J`)

Acceptance criteria:
- `rg` finds no `classical`, `noncomputable`, `Classical.*`.
- `lake env lean RevHalt/Theory/PrimitiveHolonomy_instance.lean` succeeds.
- `#print axioms` says the new declarations "do not depend on any axioms".
