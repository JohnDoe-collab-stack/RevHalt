# RevHalt

Lean 4 (Mathlib) formalization of a framework where a “reverse” verdict is forced to coincide with standard halting once it is routed through a closure operator.

Core message:

- T1 (rigidity): any valid kit is forced to agree with `Halts` on every trace (kit power collapses).
- T2 (uniform barrier): no single internal predicate can uniformly totalize/correctly/complete-decide that verdict (diagonalization).
- T3 (local power): sound extensions exist instance-by-instance, including a two-sided form where the branch is carried by a certificate (Fork/oracle), not computed uniformly.

This project does not claim a stronger decider. It formalizes:
- where “power cannot live” (kits, once forced to be correct on monotone traces),
- where it cannot be made uniform (internalization),
- where it can live safely (local certified extensions and bifurcations).

---

## One-line contract

If a kit is correct on monotone traces, then after precomposing with the monotone closure `up`, the resulting verdict is forced to be exactly standard halting.

This is the source of T1 rigidity.

---

## Core objects

### Traces and halting

- Trace: `Trace := ℕ → Prop`
- Halting: `Halts (T : Trace) : Prop := ∃ n, T n`

### The monotone closure `up`

`up` canonically monotonizes any trace:

- `(up T) n` means: “T was true at or before time n”
- `up T` is monotone in time
- existential content is preserved exactly: `Halts (up T) ↔ Halts T`

Intuition: `up` forgets non-monotone timing details and retains only “an event occurred at some time”.

Structural viewpoint: `up` is a closure operator on traces:
- extensive: `T ≤ up T`
- monotone (as an operator): `T ≤ U` implies `up T ≤ up U`
- idempotent: `up (up T) = up T`

This closure viewpoint is what makes “rigidity” a theorem rather than a slogan.

### Kits and the minimal correctness condition

A kit is just a projection on traces:

- `structure RHKit where Proj : Trace → Prop`

A kit is considered valid when it is correct on monotone traces:

- `DetectsMonotone K := ∀ X, Monotone X → (K.Proj X ↔ Halts X)`

Crucial point: this condition does not restrict `K` on non-monotone traces.
But `Rev0_K` will only feed monotone traces into `K` (because of `up`).

### Reverse halting

Define the “reverse” verdict by precomposing the kit with `up`:

- `Rev0_K K T := K.Proj (up T)`

---

## Main results (T1–T3)

### T1 — Rigidity / canonicity

Because `up T` is always monotone, `DetectsMonotone` applies immediately:

- `Rev0_K K T ↔ Halts (up T) ↔ Halts T`

Consequences:

- No “exotic power” can be hidden in the kit: once it is correct on monotone traces, `Rev0_K` is forced to be standard halting.
- All valid kits agree on every trace (kit-invariance): there do not exist two valid kits that differ on any input trace.

This is the core structural novelty: correctness on the closed/reflected objects plus precomposition by the closure yields uniqueness/rigidity.

### T2 — Impossibility of uniform internalization (diagonalization)

Once T1 identifies the verdict with a Σ1-style existence fact (halting), one can ask for an internal predicate `H(e)` that is:

- total (decides every code),
- correct (proves `H(e)` when the machine halts),
- complete (proves `Not (H(e))` when it does not),
- and has the r.e./semi-decidability needed to run the diagonal construction.

Using a fixed-point / diagonal bridge (Kleene style), the project derives a contradiction:

- there is no single internal uniform procedure/predicate that captures the verdict on all codes.

This is a barrier theorem: it is not about code tricks, but about the logical shape “uniformly deciding a Σ1 fact”.

### T3 — Complementarity: sound extensions exist instance-by-instance

T3 shows you can extend sound corpora by adding true but unprovable statements, locally, without contradicting T2.

Important distinction:

- T3 is stated at the level of corpora: sets of axioms with external truth (`Truth`).
- It is not (by default) a claim about a deductively closed proof system `Provable_{S}`.
- “Deciding” in T3 means: adding an axiom (membership), not producing a uniform internal decision predicate.

T3 comes in two complementary forms:

#### T3 (one-sided frontier)

Build a frontier set of new true axioms indexed by instances:

- include `encode_halt(e)` whenever `Rev(e)` holds but the base system does not prove it,
- extend a sound base corpus by union with that frontier.

This yields many sound extensions, but no uniform internal rule selecting all of them.

#### T3 (two-sided local oracle / certificate)

For each `e`, a certificate chooses one of two branches:

- either add `encode_halt(e)`,
- or add `encode_not_halt(e)`,

and the extension by that single axiom is sound (assuming the certificate is sound relative to external truth).

The certificate carries the branch. The framework never claims there is a uniform internal decider that outputs the branch.

This is the explicit quantifier swap:

- forbidden by T2: `exists H. forall e. decide(e)` (one uniform predicate),
- permitted by T3: `forall e. exists certificate/extension. decide_locally(e)` (instance-by-instance).

---

## Structural sketch (condensed)

1) `up` is a closure operator on traces: it projects any trace to a monotone one and preserves `Halts` exactly.

2) `DetectsMonotone` constrains a kit only on monotone traces; since `Rev0_K` evaluates `K` only on `up T`, the kit never sees non-closed inputs.

3) T1 follows as rigidity: `Rev0_K K T` collapses to `Halts T` for all `T`, hence verdicts are kit-invariant.

4) T2 is then a uniform impossibility: no internal predicate can totalize/correctly/complete-decide that existence fact for all codes (fixed point/diagonalization).

5) From T2 one extracts typed “gap” objects (true-but-unprovable), yielding strict extensions; this becomes fuel in the axiom-dynamics graph.

6) Fork packages two conditional branches around a pivot without global choice: left if `Truth p`, right if `Truth (Not p)`, with an exclusion principle.

7) T3 one-sided: extend a sound base by adding certified true frontier statements that are not internally provable.

8) T3 two-sided: a certificate chooses between `encode_halt(e)` and `encode_not_halt(e)`, producing a sound local extension `S2 ∪ {p}` without any uniform decider.

9) Instances (RefSystem, Ω) show the separation concretely: robust kit-invariant answers on semi-decidable cut queries while bits remain non-uniformizable; and “Bit vs Window” gives two operationally distinct but observationally equivalent readings.

---

## How the dynamics part fits (Fuel / Fork)

The project packages the T2/T3 phenomenon as an explicit dynamics on theories.

### EnrichedContext and gap witnesses

An `EnrichedContext` contains:
- internal provability `Provable`,
- external truth `Truth`,
- a halting predicate `H e` linked to `Rev0_K` at the truth level,
- and the r.e. witness needed for diagonalization.

From T2 one derives:

- `true_but_unprovable_exists`: there exists `p` with `Truth p` and `¬Provable p`,
- `GapWitness`: a typed witness `{p // Truth p ∧ ¬Provable p}`,
- `gapWitness_nonempty`: gap witnesses exist.

These gap witnesses are the unit of non-uniformity: downstream constructions are parameterized by such a witness, never by a global chooser.

### Fuel: strict moves exist

`Fuel` states that from any node `T` contained in the provable set, there exists a strict extension move:

- pick a `GapWitness`,
- extend by it,
- strictness is guaranteed because the witness is not provable.

This is “T2 provides fuel”: incompleteness is turned into a constructive existence of strict growth steps.

### Fork: bifurcation without global choice

A `Fork` is an object encoding a local bifurcation around a pivot `p`:

- left branch exists if you have `Truth p`,
- right branch exists if you have `Truth (Not p)`,
- exclusion: both extensions cannot be sound simultaneously.

This is the two-sided complementarity mechanism expressed as an object, not as a chooser.

---

## RefSystem layer and the Ω instance (why it matters)

The `RefSystem` layer connects:
- continuous cut sentences (rational comparisons),
- discrete bit sentences (digits),
- a semantic relation `Sat`,
- and a compatibility law relating bits to dyadic cut windows.

Key pattern used in the Ω instance:

- treat cuts as the computable / semi-decidable interface,
- reconstruct bits as boundaries between cuts (a window condition).

What this demonstrates:

- cut queries behave well: halting/Rev characterizes “reached q”, and is kit-invariant under kit validity,
- bit queries are not uniformly computable, but are semantically equivalent to a cut-window formulation,
- two operationally distinct “readings” (Bit vs Window) can be proven observationally indistinguishable once routed through the Rev/Halts layer.

This exemplifies the project’s separation:
- what is robust and kit-invariant (T1),
- what cannot be uniformized (T2),
- what can be safely added locally with certificates (T3 / Fork).

---

## What T3 is (and is not)

T3 provides soundness for sets of axioms:

- statement form: “for all p in S, Truth p”.

It does not automatically provide:

- a deductively closed proof relation `Provable_S`,
- or the meta-theorem “all inference rules preserve Truth”.

If one wants a proof-theoretic “decision” statement (“S proves p or S proves not p”), one must:
- define the closure of the corpus under chosen proof rules,
- and prove that those rules preserve `Truth` (soundness of the proof system).

This separation is intentional: T3 isolates the non-uniform extension phenomenon before committing to any specific proof calculus.

---

## File organization (high-level)

Entry points (intended map):

- `RevHalt/Base/Trace.lean`
  - `Trace`, `Halts`, `up`, monotonicity, `Halts (up T) ↔ Halts T`

- `RevHalt/Base/Kit.lean`
  - `RHKit`, `DetectsMonotone`, `Rev0_K`

- `RevHalt/Theory/Canonicity.lean`
  - T1 statements, kit-invariance, semantics-facing variants (bridge forms)

- `RevHalt/Theory/Impossibility.lean`
  - T2 diagonalization / fixed-point barrier

- `RevHalt/Theory/Complementarity.lean`
  - T3 one-sided / strong / two-sided (certificate) variants

- `RevHalt/Bridge/Context.lean`
  - `EnrichedContext`, r.e. hypotheses, `GapWitness`, extraction of true-but-unprovable

- `RevHalt/Dynamics/Core/Fuel.lean`
  - strict extension moves from gap witnesses (“T2 as fuel”)

- `RevHalt/Dynamics/Core/Fork.lean`
  - `Fork` object: two-sided branching without global choice

- `RevHalt/Dynamics/Core/RefSystem.lean`
  - reference systems: `Cut` / `Bit`, bit-window link, DR0/DR1-style kit invariance

- `RevHalt/Dynamics/Instances/OmegaChaitin.lean`
  - constructive Ω approximations, bit-window theorem, kit-invariance for cuts

- `RevHalt/Dynamics/Instances/OmegaComplexity.lean`
  - gap lower bound and “precision requires time” (Kolmogorov-style precursor)

(Exact filenames may differ slightly; this is the intended conceptual layout.)

---

## Build / verify

Prerequisites: Lean 4 + Mathlib (via `lake`).

Build:

- `lake build`

Check a file:

- `lake env lean RevHalt/Theory/Canonicity.lean`

---

## License / contribution

Add your license and contribution conventions here.
