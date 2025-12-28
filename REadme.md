# RevHalt

Lean 4 (Mathlib) formalization of a “reverse halting” framework where any verdict is **forced to coincide with standard halting** once it is routed through a monotone closure operator.

The project’s point is not to build a stronger decider. It isolates *where computational power cannot live*, *what cannot be made uniform*, and *what can exist safely as local certified extensions*.

**Triptych**
- **T1 (Closure Rigidity)**: any valid kit collapses to `Halts` on every trace.
- **T2 (Uniform Barrier)**: no single internal predicate uniformly total/correct/complete-decides the verdict (diagonalization).
- **T3 (Local Certified Power)**: sound extensions exist instance-by-instance; two-sided branching is certificate-carried (Fork/oracle), not computed uniformly.

---

## Core objects

### Traces and halting
- `Trace := ℕ → Prop`
- `Halts (T : Trace) : Prop := ∃ n, T n`

### The monotone closure `up`
`up` canonically monotonizes any trace:
- `(up T) n` means “`T` was true at or before time `n`”
- `up T` is monotone in time
- existence is preserved exactly: `Halts (up T) ↔ Halts T`

This exact preservation of `∃` is the structural reason everything “locks”.

### Kits and minimal correctness
A kit is a projection on traces:
- `structure RHKit where Proj : Trace → Prop`

Validity condition (only on monotone traces):
- `DetectsMonotone K := ∀ X, Monotone X → (K.Proj X ↔ Halts X)`

Crucial point: this does **not** constrain `K` on non-monotone traces—yet after defining `Rev0_K`, the kit is never applied to non-monotone traces anyway.

### Reverse halting
The “reverse” verdict:
- `Rev0_K K T := K.Proj (up T)`

---

## Main results (T1–T3)

### T1 — Closure Rigidity / Canonicity
Since `up T` is always monotone, the kit validity hypothesis applies immediately:
- `Rev0_K K T ↔ Halts (up T) ↔ Halts T`

Consequences:
- no exotic power can be hidden in the kit: once it is correct on monotone traces, `Rev0_K` is forced to be standard halting
- all valid kits agree on every trace (kit-invariance)

This is the core structural novelty: **correctness on closed objects + precomposition by a closure** yields rigidity.

---

### T2 — Impossibility of uniform internalization (diagonalization)
Once T1 identifies the verdict with a Σ₁-style existence fact, one can ask for an internal predicate `H(e)` that is:
- **total**: decides every code,
- **correct**: proves `H(e)` when the machine halts,
- **complete**: proves `Not (H(e))` when it does not,
- plus the **r.e./semi-decidability** needed for the diagonal construction.

Using a fixed-point/diagonal bridge (Kleene style), the project derives a contradiction:
- there is no single internal uniform procedure/predicate capturing the verdict on all codes.

This is a barrier theorem about the logical form “uniformly deciding a Σ₁ fact”, not about coding tricks.

---

### T3 — Complementarity: sound extensions exist instance-by-instance
T3 shows you can extend sound corpora by adding true but unprovable statements **locally**, without contradicting T2.

Important: T3 is first stated at the level of **corpora** (sets of axioms with an external truth predicate). “Deciding” means *adding an axiom*, not producing a uniform internal decision predicate.

Two forms:

#### One-sided frontier
Build a frontier of new true axioms indexed by instances:
- include `encode_halt(e)` whenever `Rev(e)` holds but the base system does not prove it
- extend a sound base corpus by union with that frontier

This yields many sound extensions, but no uniform internal rule selecting all of them.

#### Two-sided frontier (certificate-carried branching)
For each `e`, a certificate can select one branch:
- add `encode_halt(e)`, or
- add `encode_not_halt(e)`

The certificate carries the branch; the framework never claims a uniform internal decider outputs it.

This is the explicit quantifier swap:
- forbidden by T2: `∃ H, ∀ e, ...` (one uniform predicate)
- permitted by T3: `∀ e, ∃ (certificate/extension), ...` (local, instance-by-instance)

---

## Two-sided branching: OraclePick vs Fork vs Fork₂

This distinction is foundational and explicit in the development.

### OraclePick (binary certificate)
`OraclePick` chooses between two *arbitrary* propositions:
- `p = encode_halt(e)` if `Rev(e)`
- `p = encode_not_halt(e)` if `¬Rev(e)`

This is always enough to produce a **binary local extension** (`OraclePick → Edge`).

### Fork (complementary two-sided)
A `Fork` is stricter: it branches on a pivot `p` and its complement `Not p`, and it includes an **exclusion law**:
- both extensions cannot be sound simultaneously

So `OraclePick → Fork-step` requires **complementarity**:
- `encode_not_halt(e) = Not (encode_halt(e))`

### Fork₂ (generalized two-sided)
A clean conceptual improvement is to make the generalized object explicit:

- **`Fork₂`** branches on two arbitrary pivots `p_left / p_right` and carries an exclusion law.
- `Fork` is the special case `p_right = Not p_left`.

Practical takeaway:
- `OraclePick` naturally maps to the **binary layer** (Edge), and to **Fork₂** when an exclusion certificate is provided.
- `OraclePick` maps to **Fork** exactly when complementarity holds.

This separation makes “two-sided” conceptually precise: **binary vs complementary**.

(See `Examples/TwoSidedFrontier.lean` and `Dynamics/Core/Fork.lean` / `Fork2.lean`.)

---

## Structural sketch (condensed)

1) `up` is a closure operator on traces: it projects any trace to a monotone one and preserves `Halts` exactly.  
2) `DetectsMonotone` constrains a kit only on monotone traces; `Rev0_K` evaluates the kit only on `up T`.  
3) **T1**: rigidity follows; `Rev0_K` collapses to `Halts`, verdicts are kit-invariant.  
4) **T2**: uniform internalization of this Σ₁ fact is impossible (fixed point/diagonalization).  
5) From T2 one extracts typed gaps (true-but-unprovable), used as “fuel” for strict extensions.  
6) Two-sided branching is formalized structurally: binary (`OraclePick`) vs complementary (`Fork`) vs generalized (`Fork₂`).  
7) **T3**: local extensions exist (one-sided frontier and two-sided certificate-carried branching).  
8) Instances (RefSystem/Ω): demonstrate robust kit-invariance for semi-decidable interfaces (cuts), while non-uniformizable content (bits) appears only through bridges/certificates.

---

## OracleMachine architecture (a-machine / o-bridge / c-machine)

The project also formalizes an explicit architecture that localizes non-mechanical power.

### a-machine: the mechanical core
- `aMachine := Machine`
- `Converges e := ∃ x, x ∈ e.eval 0`
- `Halts (aMachine e) ↔ Converges e`

### c-machine: compilation / external choice
- `compile : List Sentence → Sentence → Code`
- `LR Γ φ := aMachine (compile Γ φ)`

This is a translation/choice layer, not the oracle.

### o-bridge: oracle localization
The only place where non-mechanical power enters is the bridge relating semantics to convergence:
- `OracleBridge Sat compile := ∀ Γ φ, SemConsequences Sat (Γset Γ) φ ↔ Converges (compile Γ φ)`

### Master theorem: Eval aligns with Rev (via T1)
With the bridge plus T1:
- `Eval Γ φ ↔ Halts (aMachine (compile Γ φ)) ↔ Rev0_K K (aMachine (compile Γ φ))`

So kits cannot be the source of extra power: it must live in the bridge/certificates.

### Architecture-level constraint (T2 reappears)
If additionally:
- `Eval Γ φ` were decidable for all `(Γ, φ)`, and
- the compiler covered all codes,

then halting would become decidable. Hence these assumptions cannot all hold simultaneously in the intended setting.

If one postulates an “internalization axiom” turning any external decider into an internal halting predicate, T2 yields a contradiction: local/external decisions do not become uniform/internal without breaking consistency.

---

## Dynamics (Fuel / Gap / Fork)

### EnrichedContext and gap witnesses
An `EnrichedContext` contains:
- internal `Provable`
- external `Truth`
- a halting predicate `H e` linked to `Rev0_K` at truth level
- the r.e. witness needed for diagonalization

From T2:
- `true_but_unprovable_exists`
- `GapWitness := {p // Truth p ∧ ¬Provable p}`

Gap witnesses are the “unit of non-uniformity”: downstream constructions are parameterized by a witness, never by a global chooser.

### Fuel: strict moves exist
From a node contained in the provable set, there exists a strict extension move:
- choose a `GapWitness`
- extend by it
- strictness holds because the witness is not provable

This is “T2 provides fuel”.

### Fork: bifurcation without global choice
A `Fork` around pivot `p`:
- left branch requires `Truth p`
- right branch requires `Truth (Not p)`
- exclusion: both branches cannot be sound simultaneously

Two-sided branching is thus an object with laws, not a decider.

---

## RefSystem and the Ω instance (why it matters)

`RefSystem` connects:
- continuous **Cut** sentences (rational comparisons)
- discrete **Bit** sentences (digits)
- a semantic relation `Sat`

Pattern used in Ω:
- treat cuts as the computable / semi-decidable interface
- reconstruct bits as boundaries between cuts (window condition)

So Ω exhibits the separation concretely:
- cut queries behave well and are kit-invariant under validity
- bit queries are not uniformly computable, but relate to cut windows semantically

---

## File organization (high-level)

- `RevHalt/Base/Trace.lean`: `Trace`, `Halts`, `up`, monotonicity, `Halts (up T) ↔ Halts T`
- `RevHalt/Base/Kit.lean`: `RHKit`, `DetectsMonotone`, `Rev0_K`
- `RevHalt/Theory/Canonicity.lean`: T1, kit-invariance, semantic-facing variants
- `RevHalt/Theory/Impossibility.lean`: T2 diagonalization / fixed-point barrier
- `RevHalt/Theory/Complementarity.lean`: T3 one-sided / two-sided variants, `OraclePick`
- `RevHalt/Theory/OracleMachine.lean`: a-machine / c-machine / o-bridge, architecture-level constraints
- `RevHalt/Bridge/Context.lean`: `EnrichedContext`, r.e. hypotheses, `GapWitness`
- `RevHalt/Dynamics/Core/Fuel.lean`: “T2 as fuel”
- `RevHalt/Dynamics/Core/Fork.lean`: `Fork` object (complementary two-sided)
- `RevHalt/Dynamics/Core/Fork2.lean`: `Fork₂` object (generalized two-sided)
- `RevHalt/Dynamics/Core/RefSystem.lean`: cuts/bits, DR0/DR1-style statements
- `RevHalt/Examples/CutInvariance.lean`: cut kit-invariance demo
- `RevHalt/Examples/BitWindowTheorem.lean`: Bit ↔ Win equivalence demo
- `RevHalt/Examples/TwoSidedFrontier.lean`: OraclePick (binary) vs Fork (complementary) demo

(Exact filenames may differ slightly; this is the intended map.)

---

## Build / verify

Prerequisites: Lean 4 + Mathlib (via `lake`).

- `lake build`
- `lake env lean RevHalt/Theory/Canonicity.lean`

---

## License / contribution

Add your license and contribution conventions here.
