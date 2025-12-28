# RevHalt

Lean 4 (Mathlib) formalization of a framework where a “reverse” verdict is forced to coincide with standard halting once it is routed through a monotone closure operator.

Triptych (the point of the project):
- T1 (rigidity): any valid kit is forced to agree with `Halts` on every trace (kit power collapses).
- T2 (uniform barrier): no single internal predicate can uniformly totalize/correctly/complete-decide the verdict (diagonalization).
- T3 (local power): sound extensions exist instance-by-instance, including a two-sided form where the branch is carried by a certificate (Fork/oracle), not computed uniformly.

So the project does not “invent a stronger decider”: it proves where power cannot live (kits), where it cannot be uniform (internalization), and where it can live safely (local certified extensions / bridges).

---

## Core objects

### Traces and halting

- Trace: `Trace := ℕ → Prop`
- Halting: `Halts (T : Trace) : Prop := ∃ n, T n`

### The monotone closure `up`

`up` canonically monotonizes any trace:

- `(up T) n` means: “T was true at or before time n”
- `up T` is monotone in time
- existence is preserved exactly: `Halts (up T) ↔ Halts T`

This exact preservation of `∃` is the structural reason everything “locks”.

### Kits and the minimal correctness condition

A kit is just a projection on traces:

- `structure RHKit where Proj : Trace → Prop`

A kit is considered valid when it is correct on monotone traces:

- `DetectsMonotone K := ∀ X, Monotone X → (K.Proj X ↔ Halts X)`

This condition does not restrict `K` on non-monotone traces. The punchline is that after `Rev` is defined, the framework never lets the kit see non-monotone traces.

### Reverse halting

Define the “reverse” verdict by precomposing the kit with `up`:

- `Rev0_K K T := K.Proj (up T)`

---

## Main results (T1–T3)

### T1 — Rigidity / canonicity

Because `up T` is always monotone, `DetectsMonotone` applies immediately:

- `Rev0_K K T ↔ Halts (up T) ↔ Halts T`

Consequences:
- no “exotic power” can be hidden in the kit: once it is correct on monotone traces, `Rev0_K` is forced to be standard halting
- all valid kits agree on every trace (kit-invariance)

This is the core structural novelty: correctness on reflected/closed objects plus precomposition by the closure yields uniqueness/rigidity.

### T2 — Impossibility of uniform internalization (diagonalization)

Once T1 identifies the verdict with a Σ1-style existence fact (halting), one can ask for an internal predicate `H(e)` that is:
- total (decides every code),
- correct (proves `H(e)` when the machine halts),
- complete (proves `Not (H(e))` when it does not),
- plus the required r.e./semi-decidability needed to run the diagonal construction.

Using a fixed-point / diagonal bridge (Kleene style), the project derives a contradiction:
- there is no single internal uniform procedure/predicate that captures the verdict on all codes.

This is a barrier theorem: it is not about code tricks, but about the logical shape “uniformly deciding a Σ1 fact”.

### T3 — Complementarity: sound extensions exist instance-by-instance

T3 shows you can extend sound corpora by adding true but unprovable statements, locally, without contradicting T2.

Important: T3 is first stated at the level of corpora (sets of axioms with external truth). “Deciding” is by adding an axiom (membership), not by producing a uniform internal decision predicate.

Two forms are central:

#### One-sided frontier

Build a frontier set of new true axioms indexed by instances:
- include `encode_halt(e)` whenever `Rev(e)` holds but the base system does not prove it
- extend a sound base corpus by union with that frontier

This yields many sound extensions, but no uniform internal rule selecting all of them.

#### Two-sided (local oracle) frontier

For each `e`, a certificate can choose one of two branches:
- either add `encode_halt(e)`
- or add `encode_not_halt(e)`

The certificate carries the branch; the framework never claims there is a uniform internal decider that outputs the branch.

This is the explicit quantifier swap:
- forbidden by T2: `exists H, forall e, ...` (one uniform predicate)
- permitted by T3: `forall e, exists (certificate/extension), ...` (local, instance-by-instance)

### Two-sided = Fork (certificate-carried branch)

The two-sided mechanism comes in two forms:

**Binary bifurcation**: `OraclePick` chooses between `encode_halt(e)` and `encode_not_halt(e)` (arbitrary propositions). No exclusion is guaranteed.

**Complementary bifurcation (Fork)**: `OraclePick` chooses between `p` and `Not p` (true complementarity). Fork provides exclusion: both extensions cannot be sound simultaneously.

Key points:
- no `Decidable`, no global chooser
- certificate carries the branch, not computed
- `OraclePick → Edge` always valid (binary)
- `OraclePick → Fork-step` requires `encode_not_halt = Not encode_halt`

This distinction is formalized in `Examples/TwoSidedFrontier.lean`.

---

## Structural sketch (condensed)

1) `up` is a closure operator on traces: it canonically projects any trace to a monotone one and preserves `Halts` exactly.  
2) `DetectsMonotone` constrains a kit only on monotone traces; since `Rev0_K` evaluates `K` only on `up T`, the kit never sees non-closed inputs.  
3) T1 follows as rigidity: `Rev0_K K T` collapses to `Halts T` for all `T`, hence verdicts are kit-invariant.  
4) T2 is then a uniform impossibility: no internal predicate can totalize/correctly/complete-decide that existence fact for all codes (fixed point/diagonalization).  
5) From T2 one extracts typed “gap” objects (true-but-unprovable), yielding strict extensions: this becomes fuel in the axiom-dynamics graph.  
6) Fork packages two conditional branches around a pivot without global choice: left if `Truth p`, right if `Truth (Not p)`, with an exclusion principle.  
7) T3 one-sided: extend a sound base by adding certified true frontier statements that are not internally provable.  
8) T3 two-sided: a certificate chooses between `encode_halt e` and `encode_not_halt e`, producing a sound local extension `S2 ∪ {p}` without any uniform decider.  
9) Instances (RefSystem, Ω): show the separation concretely—robust kit-invariant answers on semi-decidable cut queries while bits remain non-uniformizable.

---

## OracleMachine architecture (a-machine / o-bridge / c-machine)

This project also formalizes an explicit architecture that makes the localization of “non-mechanical power” precise.

### a-machine: the mechanical core

- `aMachine := Machine`
- `Converges e := ∃ x, x ∈ e.eval 0`
- `Halts (aMachine e) ↔ Converges e`

This fixes a purely mechanical substrate.

### c-machine: compilation / external choice

A compiler turns effective inputs into executable codes:

- `compile : List Sentence → Sentence → Code`
- `LR Γ φ := aMachine (compile Γ φ)`

This is not the oracle. It is a translation / choice layer.

### o-bridge: the oracle localization

The only place where non-mechanical power enters is the bridge relating semantics to convergence:

- `OracleBridge Sat compile := ∀ Γ φ, SemConsequences Sat (Γset Γ) φ ↔ Converges (compile Γ φ)`

This isolates oracle power into `Sat` and the bridge property.

### Master theorem: Eval is forced to agree with Rev (via T1)

With the bridge plus T1, one gets:

- `Eval Γ φ ↔ Halts (aMachine (compile Γ φ)) ↔ Rev0_K K (aMachine (compile Γ φ))`

So kits cannot be the source of “extra power”: any such power must live in the bridge/certificates, not in `K`.

### Why this matters: architecture-level constraints

If additionally:
- `Eval Γ φ` were decidable for all `(Γ, φ)`, and
- the compiler covered all codes (surjective coverage),

then halting would become decidable. Therefore these assumptions cannot hold simultaneously in the intended setting.

Finally, if one postulates an “internalization axiom” that turns any external decider into an internal halting predicate, T2 yields a contradiction. This is the architecture-level form of the uniform barrier: local/external decisions do not become uniform/internal without breaking consistency.

---

## How the dynamics part fits (Fuel / Fork)

### EnrichedContext and gap witnesses

An `EnrichedContext` contains:
- an internal provability predicate `Provable`
- an external truth predicate `Truth`
- a halting predicate `H e` linked to `Rev0_K` at the truth level
- the r.e. witness needed for diagonalization

From T2 one derives:
- `true_but_unprovable_exists`: exists `p` with `Truth p` and `¬Provable p`
- `GapWitness`: typed witness `{p // Truth p ∧ ¬Provable p}`
- `gapWitness_nonempty`: gap witnesses exist

These witnesses are the “unit of non-uniformity”: everything downstream is parameterized by a witness, never by a global chooser.

### Fuel: strict moves exist

`Fuel` states that from any node `T` contained in the provable set, there exists a strict extension move:
- pick a `GapWitness`
- extend by it
- strictness holds because the witness is not provable

This is “T2 provides fuel”: incompleteness becomes a constructive existence of strict growth steps.

### Fork: bifurcation without global choice (two-sided complementarity)

A `Fork` is an object encoding a local bifurcation around a pivot `p`:

- left branch exists if you have `Truth p`
- right branch exists if you have `Truth (Not p)`
- exclusion: both branches cannot be sound simultaneously

This is the two-sided complementarity mechanism as an object, not a chooser.

---

## RefSystem layer and the Ω instance (why it matters)

The `RefSystem` layer connects:
- continuous Cut sentences (rational comparisons)
- discrete Bit sentences (digits)
- a semantic relation `Sat`

The pattern used in the Ω instance:
- treat cuts as the computable / semi-decidable interface
- reconstruct bits as boundaries between cuts (a window condition)

So the Ω instance exhibits the philosophy concretely:
- cut queries behave well: halting/Rev characterizes “reached q”, and verdicts are kit-invariant under validity
- bit queries are not uniformly computable, but relate to cut windows at the semantic level

This exemplifies the separation:
- what is robust and kit-invariant (T1),
- what cannot be uniformized (T2),
- what can be safely added locally with certificates (T3 / Fork).

---

## File organization (high-level)

- `RevHalt/Base/Trace.lean`
  - `Trace`, `Halts`, `up`, monotonicity, `Halts (up T) ↔ Halts T`

- `RevHalt/Base/Kit.lean`
  - `RHKit`, `DetectsMonotone`, `Rev0_K`

- `RevHalt/Theory/Canonicity.lean`
  - T1 statements, kit-invariance, semantics-facing variants

- `RevHalt/Theory/Impossibility.lean`
  - T2 diagonalization / fixed-point barrier

- `RevHalt/Theory/Complementarity.lean`
  - T3 one-sided / two-sided / strong variants, `OraclePick`, frontier constructions

- `RevHalt/Theory/OracleMachine.lean`
  - a-machine / c-machine / o-bridge separation, `Eval ↔ Halts ↔ Rev`, architecture-level constraints

- `RevHalt/Bridge/Context.lean`
  - `EnrichedContext`, r.e. hypotheses, `GapWitness`, `true_but_unprovable_exists`

- `RevHalt/Dynamics/Core/Fuel.lean`
  - “T2 as fuel”: strict extension moves via gap witnesses

- `RevHalt/Dynamics/Core/Fork.lean`
  - `Fork` as a local two-sided bifurcation object (no global choice)

- `RevHalt/Dynamics/Core/RefSystem.lean`
  - reference systems: `Cut` / `Bit` families, compatibility, DR0/DR1-style statements

- `RevHalt/Dynamics/Instances/OmegaChaitin.lean`
  - constructive Ω approximations, `omega_bit_cut_link`, kit-invariance for cuts, Bit/Win window equivalences

- `RevHalt/Dynamics/Instances/OmegaKolmogorov.lean`
  - gap lower bound, “precision requires time” (Kolmogorov-style bound)

(Exact filenames may differ slightly; this list is the intended map.)

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
