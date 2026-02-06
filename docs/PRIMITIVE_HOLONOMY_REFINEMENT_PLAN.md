# PrimitiveHolonomy Refinement Plan (Gauge + 1D Shots, Constructive)

Goal: keep `RevHalt/Theory/PrimitiveHolonomy.lean` maximally permissive (many models),
while making the "no-go" statements (`Obstruction*`, "ordinal/time is insufficient")
non-vacuous and composable, without adding any classical reasoning, choice, or
quantifier-negation swaps.

This plan is additive: it introduces *layered* notions (admissible gauges, admissible
1D shots) and leaves the current core definitions intact.

Status:
- Implemented in `RevHalt/Theory/PrimitiveHolonomy.lean` (additive definitions + lemmas).
- This document remains the reference for *why* these layers exist and how to use them.

## 0. Current Status (Rigor Check)

Facts we can currently prove *constructively* (no cheating):

1. `Obstruction` is degenerate under the current `Gauge`.
   - `Gauge` is any relation-valued repair on the target fiber.
   - An `emptyGauge` (always `False`) is definable for any `obs/target_obs`.
   - For `emptyGauge`, `CorrectedTransport` and `CorrectedHolonomy` are empty,
     so a *twist witness* can never exist.
   - Therefore `Obstruction sem obs target_obs J` is refutable for every `J`
     by instantiating the universal quantifier at `emptyGauge`.
   - Theory-level statement: `not_Obstruction_of_emptyGauge` (uses
     `not_correctedTransport_emptyGauge` / `not_correctedHolonomy_emptyGauge`).
   - The instance file also demonstrates it as `not_obstruction_any`.

2. `NonReducibleHolonomy` (quantifying over all `Q` and all `Summary q`) is too strong
   if "1D shot" is unrestricted.
   - Because `q : Path h k -> Q` is completely free, one can pick a `Q` that encodes
     the path itself (and endpoints), then define `H` to replay `HolonomyRel`.
   - So the interesting claim is not "no summary exists", but "no *time-like* summary
     exists" (ordinal/shadow style).

3. `HolonomyRel` ignores the 2-cell proof term `α` (it depends only on `(p,q)`).
   - This is not a bug by itself, but it means "two different deformations between the
     same 1-paths" are indistinguishable at the holonomy level.

All of the above are mathematical properties of the current definitions, not artifacts
of the toy model.

## 1. Design Principles

1. Keep the existing core defs (`Gauge`, `AutoRegulated`, `Obstruction`, `Summary`,
   `FactorsHolonomy`, `NonReducibleHolonomy`) unchanged for maximum model perimeter.
2. Add *refined* predicates/variants that encode the intended restrictions as data.
3. Stay strictly constructive: no `classical`, no `noncomputable`, no hidden choice.
4. Prefer "positive"/witnessed notions over bare negations when possible.

## 2. Gauges: Make Obstruction Non-Vacuous Without Shrinking Models

### 2.1 Add a Canonical `emptyGauge` (Theory-Level)

In `RevHalt/Theory/PrimitiveHolonomy.lean`, add:

- `def emptyGauge (obs) (target_obs) : Gauge obs target_obs := ...` (always `False`)
- Lemmas (all by unfolding):
  - `not_correctedTransport_emptyGauge : ¬ CorrectedTransport ... (emptyGauge ...) ...`
  - `not_correctedHolonomy_emptyGauge : ¬ CorrectedHolonomy ... (emptyGauge ...) ...`
  - `theorem not_Obstruction_of_emptyGauge : ¬ Obstruction sem obs target_obs J`

This does not change the meaning of anything; it just makes the degeneracy explicit
in the theory file (so we do not "discover it by accident" in models).

If you do not want to add the global `¬ Obstruction` lemma to the theory file, at least
add the `emptyGauge` definition plus the "CorrectedHolonomy is empty" lemma, and keep
the global refutation in the instance file.

### 2.2 Introduce "Admissible Gauges" as a Predicate

Define one or more admissibility predicates (do not pick just one yet):

- `GaugeRefl φ` (non-annihilation via diagonal):
  - For every path `p` and every fiber point `y`, `φ p y y`.
- `GaugeTotal φ` (non-annihilation via seriality):
  - For every path `p` and fiber point `y`, there exists `y'` with `φ p y y'`.

These are constructive and keep models broad: a model can *choose* which class of
gauges it considers "allowed" without modifying the base `Gauge`.

### 2.3 Parameterize Auto-Regulation and Obstruction by Admissibility

Add parameterized variants (names are suggestions):

- `AutoRegulatedWrt (OK : Gauge -> Prop) J : Prop :=
    ∃ φ, OK φ ∧ (diagonalization over J with φ)`

- `ObstructionWrt (OK : Gauge -> Prop) J : Prop :=
    ∀ φ, OK φ -> ∃ c ∈ J, (twist witness for CorrectedHolonomy with φ at c)`

Prove constructively:

- `ObstructionWrt OK J -> ¬ AutoRegulatedWrt OK J`
- `AutoRegulatedWrt OK J -> ¬ ObstructionWrt OK J`

Then recover the old defs as a special case:

- `AutoRegulated J` is `AutoRegulatedWrt (fun _ => True) J`
- `Obstruction J` is `ObstructionWrt (fun _ => True) J`

But now you can also talk about meaningful obstructions by choosing `OK := GaugeRefl`
or `OK := GaugeTotal` (or something else).

### 2.4 Optional: Quantify "Failure of Diagonalization" (Hole vs Twist)

If you want to avoid restricting gauges at all, add a second, orthogonal improvement:
measure *how* diagonalization fails for a relation `R : X -> X -> Prop`:

- `Hole(R) := ∃ x, ¬ R x x`
- `Twist(R) := ∃ x x', x ≠ x' ∧ R x x'`
- `Defect(R) := Hole(R) ∨ Twist(R)`

Then define a defect-based obstruction:

- `ObstructionDefect J := ∀ φ, ∃ c ∈ J, Defect (CorrectedHolonomy ... φ ... )`

This makes "emptyGauge" a *failure by holes* rather than a "get out of jail" card.
It is still strictly constructive (witnessed by `∃`).

## 3. 1D Shots: Make "Ordinal/Time Insufficiency" Non-Trivial

### 3.1 Define a Time-Like Shot as Data on Objects (Not on Paths)

Add a structure:

- `TimeShot (A) [Preorder A]` with:
  - `time : P -> A`
  - `mono : Reach h k -> time h ≤ time k`

Define its associated summary (path ignored, endpoint only):

- `TimeShot.toSummary : Summary A := fun {h k} _p => time k`

Now define "factors through time":

- `FactorsHolonomyTime shot := FactorsHolonomy sem obs target_obs shot.toSummary`

And the non-reduction statement relative to time-shots:

- `NonReducibleHolonomyTime := ∀ A [Preorder A] (shot : TimeShot A),
    ¬ FactorsHolonomy sem obs target_obs shot.toSummary`

This blocks the trivial "encode the whole path" escape hatch: the code depends only on
the target object (time coordinate), not on the chosen path.

### 3.2 Relate Scheduling to a Constructive "Shadow Shot"

Scheduling gives `c : A -> P` and `cofinal : ∀ h, ∃ i, Reach h (c i)`, but does not
construct a choice function `P -> A`. Constructively, the canonical shadow is set-valued:

- `shadowFuture (s : Scheduling A) (h : P) : Set A := { i | Reach h (s.c i) }`

Then define a summary with `Q := Set A`:

- `shadowSummary (s) : Summary (Set A) := fun {h k} _p => shadowFuture s k`

This is "on n'exclut rien": a path can traverse many indices, so we record the whole
future-set of indices compatible with the endpoint.

Then define:

- `FactorsHolonomyShadow s := FactorsHolonomy sem obs target_obs (shadowSummary s)`
- `NonReducibleHolonomyShadow := ∀ A [Preorder A] (s : Scheduling A),
    ¬ FactorsHolonomy sem obs target_obs (shadowSummary s)`

This is the cleanest constructive connection between ordinals/scheduling and `Summary`
without adding choice.

## 4. What To Do With `NonReducibleHolonomy` (Unrestricted)

Keep it, but treat it as a deliberately "maximally quantified" statement that is not the
right target for ordinal/time claims.

Concrete doc action:

- Add a short note in `RevHalt/Theory/PrimitiveHolonomy.lean` near
  `NonReducibleHolonomy` explaining that unrestricted summaries can encode the full path,
  so the interesting theorem is the *restricted* one (`NonReducibleHolonomyTime` or
  `NonReducibleHolonomyShadow`).

## 5. Instance File Follow-Up (Optional)

After the theory-level refinements exist, extend
`RevHalt/Theory/PrimitiveHolonomy_instance.lean` to also show:

1. `ObstructionWrt GaugeRefl ...` can become nontrivial (or still fails, depending on
   semantics), and the reason is now visible.
2. A concrete `TimeShot Nat` or `shadowSummary toyScheduling` and a proof that holonomy
   does not factor through it (if you want an "ordinal insufficiency" witness).

This remains optional; the current instance already stress-tests holonomy/lag and
`¬ FactorsHolonomy` for one very weak shot.

## 6. Validation Checklist

After implementing, run:

- `rg -n \"\\b(classical|Classical|noncomputable)\\b\" RevHalt/Theory/PrimitiveHolonomy.lean`
- `lake env lean RevHalt/Theory/PrimitiveHolonomy.lean`
- `lake env lean RevHalt/Theory/PrimitiveHolonomy_instance.lean`
- `#print axioms` for the new refined defs/lemmas to confirm no axioms creep in.
