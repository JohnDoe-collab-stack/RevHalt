# RevHalt

RevHalt is a Lean 4 (Mathlib) formalization of a single idea:

**Turn an impossibility (undecidability of halting) into a navigable structure.**

Instead of treating the Halting Theorem as a dead-end (“you can’t know, period”), RevHalt isolates what is **rigid**, what is **uniformly impossible**, and what is **locally extendable with certificates**, and packages this into a clean dynamics on theories.

## What is actually new 

RevHalt is **not** “just an oracle” and **not** “just Gödel again”.
The novelty is **structural**:

- **Oracle decomposed**: instead of postulating a black‑box, RevHalt exposes a minimal
  correctness condition (`DetectsMonotone`) + a closure operator (`up`) that **forces**
  any valid observer to collapse to standard halting (rigidity).
- **Beyond existence**: Gödel shows *there exist* true‑but‑unprovable statements.
  RevHalt gives a **systematic, instance‑wise mechanism** (T3 + certificates) and a
  **dynamic** on theories (chains / forks) to navigate them.
- **P1 Extraction (Stabilization)**: Standard theories treat "never halting" as a logical negation. RevHalt treats it as a **geometric certificate**: the failure of a monotone detector (`¬ Rev0_K`) is formally a proof of stabilization. This extracts $\Pi_1$ structure directly from the instrument, without needing Omega.

If you want a slogan: **RevHalt is a geometry of the oracle, not a new oracle.**

---

## What this is useful for (in one page)

RevHalt gives three concrete utilities:

1) **Safety / anti-magic (T1 — Rigidity).**  
   If a “kit” claims to detect halting but is only required to be correct on the **monotone closure** of traces, then it is forced to collapse to standard halting.  
   This is a *security theorem*: there is no hidden exotic power once you impose the minimal correctness condition.

2) **Exact internal limits (T2 — Uniform barrier).**  
   RevHalt pins down why a system cannot **uniformly internalize** its own halting verdict as a total+correct+complete predicate (under the standard r.e. hypotheses needed for diagonalization).  
   This is not “code trickery”: it is a barrier about *uniformly packaging Σ₁ existence + Π₁ stabilization* into one internal predicate.

3) **Local certified progress (T3 — Fork / local power).**  
   Although uniform decision is impossible, you can still make **sound progress instance-by-instance**:
   - extract **true-but-unprovable** facts as *typed witnesses* (`GapWitness`)
   - use them as **fuel** for strict, sound extensions
   - navigate uncertainty via **certificate-carried branching** (`Fork`), without any global `Decidable` chooser.

The payoff is an explicit framework for systems (proof assistants, verification architectures, “self-checking” designs) that must operate at the boundary of what is computable: replace “fatal unknown” with “certified bifurcation + sound extension steps”.

---

## Core objects

### Traces and halting

```lean
Trace := ℕ → Prop
Halts (T : Trace) : Prop := ∃ n, T n
````

### The monotone closure `up`

`up` canonically “monotonizes” any trace:

```lean
up (T : Trace) : Trace := fun n => ∃ k ≤ n, T k
```

Key facts:

* `up T` is monotone in time
* existence is preserved exactly: `Halts (up T) ↔ Halts T`

This *exact preservation of ∃* is the structural reason the rigidity theorem locks in.

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

* **No kit can “hide power”**: once correct on closed/monotone traces, `Rev0_K` is forced to equal `Halts`.
* **Kit-invariance**: all valid kits agree on every trace.

This is the core structural novelty: correctness on the “closed” image of a closure operator forces a unique extension to all inputs.

### T2 — Uniform barrier (diagonalization)

After T1, the verdict is a Σ₁-style existence property (halting).

But “deciding halting” is not just Σ₁. Uniform *decision* implicitly tries to control both sides:

- Σ₁ side (witness / existence): `Halts T` is of the form `exists n, T n`
- Π₁ side (stabilization / never): `Not (Halts T)` is of the form `forall n, not (T n)`

The decisive barrier is the Π₁ side: “no witness will ever appear” is a stabilization claim.

T2 proves: there is **no single internal predicate** `H(e)` that is simultaneously

* total (decides all codes),
* correct (proves `H(e)` when the machine halts),
* complete (proves `Not (H(e))` when it does not),
* and r.e./semi-decidable in the way needed to run the diagonal/fixed-point construction.

Result: **uniform internalization is impossible**.

In other words: you cannot uniformly compress “Σ₁ witness when it halts” + “Π₁ stabilization when it doesn’t”
into one internal, mechanically controlled interface without triggering diagonalization.

### T3 — Local certified power (extensions + branching)

T3 turns the barrier into usable structure:

* From T2 one extracts **true but unprovable** statements as *typed objects*:

  ```lean
  GapWitness ctx := { p : PropT // Truth p ∧ ¬Provable p }
  ```

* These witnesses yield **strict sound extensions** (“fuel”):
  you can extend a sound node by a true unprovable proposition, and strictness is guaranteed.

* Two-sided navigation is packaged as **Fork** (certificate-carried branching).
  This is exactly “Σ₁ vs Π₁”, but *locally* and *by certificates*, not by a global decider:

  * left branch: a certificate `Truth p` (think: Σ₁-style witness / existence)
  * right branch: a certificate `Truth (Not p)` (this is the **Stabilization Certificate** derived from `¬ Rev0_K`)
  * exclusion: both certificates cannot co-exist in a single sound node

No global decision procedure is assumed; the branch is carried by a certificate, not computed.

---

## Two-sided branching done correctly: OraclePick vs Fork vs Fork2

RevHalt distinguishes *binary choice* from *logical complementarity*.

### OraclePick (binary, always)

`OraclePick` chooses between two arbitrary propositions:

This is *not* yet Σ₁ vs Π₁. It is only a binary selection.
To recover the real “two-side barrier” you need complementarity (p vs Not p),
which is where the Π₁ stabilization meaning actually enters.

* either `p = encode_halt e`
* or `p = encode_not_halt e`

This always yields a local extension step (`OraclePick → Edge`), but it does **not** by itself give exclusion.

### Fork (complementary, with exclusion)

`Fork` is branching on `p` versus `Not p`.
To interpret an `OraclePick` as a genuine `Fork`, you need the **complementarity condition**:

```lean
encode_not_halt e = Not (encode_halt e)
```

Then OraclePick becomes a Fork-step and exclusion follows.

### Fork2 (generalized two-pivot fork)

If you want two-sided branching on arbitrary pivots `p_left` / `p_right` with an exclusion law,
use a generalized `Fork2`. This matches OraclePick *without* forcing `p_right = Not p_left`.

---

## OracleMachine architecture (where non-mechanical power lives)

RevHalt makes the “oracle location” explicit:

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

## Examples (why this is not “just philosophy”)

RevHalt’s instance layer demonstrates the separation on real objects:

* **Cut invariance:** cut-queries are kit-invariant under validity (DR1-style results).
* **Bit ↔ Window equivalence:** two operationally distinct sentences become observationally equivalent.
* **Ω instance:** treat cuts as the semi-decidable interface and reconstruct bits as boundaries between cuts.

These examples show: you can get robust, kit-invariant answers on the semi-decidable interface,
while non-uniformizable bit-level content remains non-uniform (exactly as predicted by T2/T3).

---

## File map (high level)

* `RevHalt/Base/Trace.lean` — `Trace`, `Halts`, `up`, monotonicity, `Halts (up T) ↔ Halts T`
* `RevHalt/Base/Kit.lean` — `RHKit`, `DetectsMonotone`, `Rev0_K`
* `RevHalt/Theory/Canonicity.lean` — T1 (`T1_traces`, `T1_uniqueness`)
* `RevHalt/Theory/Impossibility.lean` — T2 (diagonal/fixed-point barrier)
* `RevHalt/Theory/Complementarity.lean` — T3, `OraclePick`, frontier constructions
* `RevHalt/Bridge/Context.lean` — `EnrichedContext`, `Truth`, `GapWitness`, true-but-unprovable extraction
* `RevHalt/Dynamics/Core/Fuel.lean` — strict extension moves from gap witnesses
* `RevHalt/Dynamics/Core/Fork.lean` — `Fork.ofPivot`, exclusion
* `RevHalt/Dynamics/Core/RefSystem.lean` — `Cut`/`Bit`/`Win`, DR0/DR1-style transport
* `RevHalt/Dynamics/Instances/OmegaChaitin.lean` — Ω approximation + cut/bit/window theorems
* `RevHalt/Theory/OracleMachine.lean` — a-machine / c-machine / o-bridge, architecture-level constraints

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

