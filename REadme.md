# RevHalt

RevHalt is a Lean 4 (Mathlib) formalization of a single idea:

**Turn an impossibility (undecidability of halting) into a navigable structure.**

Instead of treating the Halting Theorem as a dead-end ("you can't know, period"), RevHalt isolates what is **rigid**, what is **uniformly impossible**, and what is **locally extendable with certificates**, and packages this into a clean dynamics on theories.

## What is actually new 

RevHalt is **not** "just an oracle" and **not** "just Gödel again".
The novelty is **structural**:

- **Oracle decomposed**: instead of postulating a black‑box, RevHalt exposes a minimal
  correctness condition (`DetectsMonotone`) + a closure operator (`up`) that **forces**
  any valid observer to collapse to standard halting (rigidity).
- **Beyond existence**: Gödel shows *there exist* true‑but‑unprovable statements.
  RevHalt gives a **systematic, instance‑wise mechanism** (T3 + certificates) and a
  **dynamic** on theories (extensions) to navigate them.
- **P1 Extraction (Stabilization)**: Standard theories treat "never halting" as a logical negation. RevHalt treats it as a **geometric certificate**: the failure of a monotone detector (`¬ Rev0_K`) is formally a proof of stabilization. This extracts Π₁ structure directly from the instrument, without needing Omega.

If you want a slogan: **RevHalt is a geometry of the oracle, not a new oracle.**

---

## Architecture: Kernel + State

RevHalt separates two distinct concerns:

- **Kernel (fixed calculus)**: `S.Provable : PropT → Prop` — the internal proof relation of the system
- **State (variable corpus)**: `S2, S3 : Set PropT` — the current set of accepted truths

This separation gives:

| Layer | Object | Meaning |
|-------|--------|---------|
| Calculus | `S.Provable p` | "p is internally derivable" |
| Corpus | `p ∈ S2` | "p is accepted/certified" |

**Key invariant**: If `¬ S.Provable p`, then p remains unprovable regardless of corpus extensions. Each `p ∈ S3` with `¬ S.Provable p` is an **absolute witness** of incompleteness.

T2 blocks uniform decision **in the calculus**.  
T3 permits instancewise extension **in the corpus**.

---

## What this is useful for (in one page)

RevHalt gives three concrete utilities:

1) **Safety / anti-magic (T1 — Rigidity).**  
   If a "kit" claims to detect halting but is only required to be correct on the **monotone closure** of traces, then it is forced to collapse to standard halting.  
   This is a *security theorem*: there is no hidden exotic power once you impose the minimal correctness condition.

2) **Exact internal limits (T2 — Uniform barrier).**  
   RevHalt pins down why a system cannot **uniformly internalize** its own halting verdict as a total+correct+complete predicate (under the standard r.e. hypotheses needed for diagonalization).  
   This is not "code trickery": it is a barrier about *uniformly packaging Σ₁ existence + Π₁ stabilization* into one internal predicate.

3) **Local certified progress (T3 — Fork / local power).**  
   Although uniform decision is impossible, you can still make **sound progress instance-by-instance**:
   - extract **true-but-unprovable** facts via oracle picks (`OraclePick`)
   - use them as **fuel** for strict, sound extensions (`S3 = S2 ∪ {pick.p}`)
   - navigate uncertainty via **certificate-carried branching**, without any global `Decidable` chooser.

The payoff is an explicit framework for systems (proof assistants, verification architectures, "self-checking" designs) that must operate at the boundary of what is computable: replace "fatal unknown" with "certified bifurcation + sound extension steps".

---

## Core objects

### Traces and halting

```lean
Trace := ℕ → Prop
Halts (T : Trace) : Prop := ∃ n, T n
```

### The monotone closure `up`

`up` canonically "monotonizes" any trace:

```lean
up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k
```

Key facts:

* `up T` is monotone in time
* existence is preserved exactly: `Halts (up T) ↔ Halts T`

This *exact preservation of ∃* is the structural reason the rigidity theorem locks in.

### Algebraic Stabilization (Kernel of `up`)

The operator `up` acts as a **projector** on traces.
Its kernel defines stabilization algebraically:

```lean
up T = ⊥ ↔ ∀ n, ¬ T n
```

This means: a trace stabilizes iff it lies in the kernel of `up` (the "bottom" trace).
Stabilization is not just a logical negation; it is **structural nullity**—the trace collapses to the zero element under the closure operator.

This is formalized in `RevHalt/Theory/Categorical.lean` (`up_eq_bot_iff`, `up_is_projector`).

### Kits and minimal correctness

A kit is a projection on traces:

```lean
structure RHKit where
  Proj : Trace → Prop
```

Validity condition:

```lean
DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ Halts X)
```

This does **not** constrain `K` on non-monotone traces — but after we define `Rev`, the kit never sees non-monotone inputs.

### Reverse halting

```lean
Rev0_K (K : RHKit) (T : Trace) : Prop := K.Proj (up T)
```

---

## The triptych (T1 / T2 / T3)

### T1 — Rigidity / canonicity

Since `up T` is always monotone, `DetectsMonotone` applies immediately:

```lean
Rev0_K K T ↔ Halts (up T) ↔ Halts T
```

Consequences:

* **No kit can "hide power"**: once correct on closed/monotone traces, `Rev0_K` is forced to equal `Halts`.
* **Kit-invariance**: all valid kits agree on every trace.

This is the core structural novelty: correctness on the "closed" image of a closure operator forces a unique extension to all inputs.

### T2 — Uniform barrier (diagonalization)

After T1, the verdict is a Σ₁-style existence property (halting).

But "deciding halting" is not just Σ₁. Uniform *decision* implicitly tries to control both sides:

- Σ₁ side (witness / existence): `Halts T` is of the form `exists n, T n`
- Π₁ side (stabilization / never): `Not (Halts T)` is of the form `forall n, not (T n)`

The decisive barrier is the Π₁ side: "no witness will ever appear" is a stabilization claim.

T2 proves: there is **no single internal predicate** `H(e)` that is simultaneously

* total (decides all codes),
* correct (proves `H(e)` when the machine halts),
* complete (proves `Not (H(e))` when it does not),
* and r.e./semi-decidable in the way needed to run the diagonal/fixed-point construction.

Result: **uniform internalization is impossible**.

In other words: you cannot uniformly compress "Σ₁ witness when it halts" + "Π₁ stabilization when it doesn't"
into one internal, mechanically controlled interface without triggering diagonalization.

### T3 — Local certified power (extensions + branching)

T3 turns the barrier into usable structure:

* **OraclePick**: For each code `e`, an explicit two-sided oracle witness packages a chosen sentence `p` together with a certificate:
  - Left branch: `Rev0_K ...` (Halting Witness) → `p = encode_halt e`
  - Right branch: `KitStabilizes ...` (Stabilization Certificate) → `p = encode_not_halt e`

* These picks yield **sound extensions**: `S3 := S2 ∪ {pick.p}` preserves soundness.

* **Quantifier Swap**: T2 forbids `∃H ∀e` (uniform internal predicate). T3 permits `∀e ∃Sₑ` (instancewise sound extension).

No global decision procedure is assumed; the branch is carried by a certificate, not computed.

---

## OracleMachine architecture (where non-mechanical power lives)

RevHalt makes the "oracle location" explicit:

* **a-machine (mechanical):** the fixed `Machine : Code → Trace`
* **c-machine (compile/choice):** `compile : List Sentence → Sentence → Code`
* **o-bridge (oracle):** the bridge linking semantics to convergence

```lean
OracleBridge Sat compile :=
  ∀ Γ φ, SemConsequences Sat (Γset Γ) φ ↔ Converges (compile Γ φ)
```

With the bridge and T1:

```lean
Eval Γ φ ↔ Halts (aMachine (compile Γ φ)) ↔ Rev0_K K (aMachine (compile Γ φ))
```

So **kits are not where the power is**. Any non-mechanical power must live in `Sat` / bridge assumptions / certificates.

---

## File map (high level)

### Base Layer
* `RevHalt/Base/Trace.lean` — `Trace`, `Halts`, `up`, monotonicity, `Halts (up T) ↔ Halts T`
* `RevHalt/Base/Kit.lean` — `RHKit`, `DetectsMonotone`, `Rev0_K`

### Theory Layer
* `RevHalt/Theory/Canonicity.lean` — T1 (`T1_traces`, `T1_uniqueness`, `T1_neg_traces`)
* `RevHalt/Theory/Impossibility.lean` — T2 (diagonal/fixed-point barrier, `InternalHaltingPredicate`, `T2_impossibility`)
* `RevHalt/Theory/Complementarity.lean` — T3, `OraclePick`, `S1Set`, `S3Set`, `T3_weak_extension_explicit`, `T3_strong`
* `RevHalt/Theory/Stabilization.lean` — `Stabilizes`, `KitStabilizes`, `T1_stabilization`, `KitStabilizes_iff_up_eq_bot`
* `RevHalt/Theory/Categorical.lean` — Order-theoretic structure: `up` as reflector, `BotTrace`, `up_eq_bot_iff`, `up_is_projector`, `Frontier`
* `RevHalt/Theory/QuantifierSwap.lean` — Quantifier Swap principle (`T3_permits_instancewise`, `quantifier_swap_coexistence`)
* `RevHalt/Theory/ThreeBlocksArchitecture.lean` — OracleMachine (a-machine, c-machine, o-bridge), `OracleBridge`, `eval_iff_rev`
* `RevHalt/Theory/WitnessLogic.lean` — `witness_soundness` (ML heuristic backing)

---

## Build

Prerequisites: Lean 4 + Mathlib (`lake`).

```bash
lake build
```

Check a file:

```bash
lake env lean RevHalt/Theory/Canonicity.lean
```

---

## License / contribution

Add your license and contribution conventions here.
