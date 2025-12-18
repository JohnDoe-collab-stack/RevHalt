# RevHalt

A Lean 4 framework that **inverts** the usual presentation of incompleteness by separating:

- a **syntactic layer** (sentences and provability), and
- a **semantic / observational layer** (external truth + an abstract observation instrument, the Kit).

Instead of starting from a fixed model and concluding “some truths escape proof”, RevHalt starts from an **observation mechanism** and proves that **no logical system can internalize the instrument’s certified verdicts**. The resulting gap is then **made explicit as typed content** and used to build sound extensions.

---

## The Inversion

| Aspect | Classical (Gödel/Turing) | RevHalt |
|--------|---------------------------|---------|
| “Truth source” | Standard model (ℕ / Turing semantics) | Abstract Kit (`RHKit`) + external `Truth` |
| What escapes | Some true statements | Kit-certified statements not internalizable by `Provable` |
| The gap | Existence-style, informal | **Typed set** `S₁ : Set PropT` |
| After incompleteness | Ad hoc extensions | **Complementarity**: `S₃ = S₂ ∪ S₁` (soundness-preserving) |

---

## Core Files

```text
RevHalt/Base/Trace.lean           # Trace := ℕ → Prop, Halts, up
RevHalt/Base/Kit.lean             # RHKit, DetectsMonotone, Rev0_K
RevHalt/Theory/Canonicity.lean    # T1: Rev0_K ↔ Halts
RevHalt/Theory/Impossibility.lean # T2: no internal predicate captures Rev0_K
RevHalt/Theory/Complementarity.lean # T3: S₁ ∪ S₂ = S₃ is sound + oracle variant
```

---

## The Kit (Observation Instrument)

```lean
structure RHKit where
  Proj : Trace → Prop

def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ ∃ n, X n)

def Rev0_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)
```

The Kit is an **abstract observation mechanism**. The only requirement is `DetectsMonotone`: on monotone traces, the Kit agrees with standard existence.

**T1 (Canonicity)**: `Rev0_K K T ↔ Halts T` for any valid Kit `K`.

Meaning: all valid Kits agree on halting, so the Kit becomes a principled *observation interface* for computational truth.

---

## The System Interface (Syntax vs Semantics)

```lean
structure ImpossibleSystem (Code PropT : Type) where
  Machine : Code → Trace       -- physical layer
  K : RHKit                    -- observation instrument
  h_canon : DetectsMonotone K  -- canonicity hypothesis (T1 applies)
  Provable : PropT → Prop      -- proof predicate (syntactic)
  diagonal_program : ...       -- diagonal bridge tied to Rev0_K
```

RevHalt treats `PropT` as an abstract syntax type and `Provable` as an abstract internal proof predicate.

Semantics is represented externally by a predicate:

* `Truth : PropT → Prop`

Soundness is always carried explicitly as hypotheses (e.g. `∀ p ∈ S2, Truth p`).

---

## The Impossibility (T2)

**T2**: no internal predicate inside the system can capture the Kit’s `Rev0_K`.

This is not “some truths escape proof” in the classical vague sense.
It is a precise statement: **this instrument’s certified verdicts cannot be internalized by the system’s internal mechanism**.

---

## The Gap as a Typed Frontier (One-Sided)

The “gap” is not left as an abstract existence claim. It is *materialized* as a set of sentences:

```lean
def S1Set (S : ImpossibleSystem Code PropT) (encode_halt : Code → PropT) : Set PropT :=
  { p | ∃ e,
      p = encode_halt e ∧
      Rev0_K S.K (S.Machine e) ∧
      ¬ S.Provable (encode_halt e) }
```

An element of `S₁` is:

* syntactically a sentence `encode_halt e : PropT`,
* semantically backed by the Kit: `Rev0_K S.K (S.Machine e)`,
* and explicitly **non-internalizable**: `¬ S.Provable (encode_halt e)`.

This is a *typed description of the frontier*.

---

## Complementarity (One-Sided): `S₃ = S₂ ∪ S₁`

Given a sound base corpus `S₂ : Set PropT` with explicit witness:

* `h_S2_sound : ∀ p ∈ S2, Truth p`

define the extension:

```lean
def S3Set (S : ImpossibleSystem Code PropT) (S2 : Set PropT) (encode_halt : Code → PropT) : Set PropT :=
  S2 ∪ S1Set S encode_halt
```

**T3 (Weak, one-sided)**: from a single witness `(e, hKit, hUnprov)` plus an explicit correctness bridge
`Rev0_K ... → Truth (encode_halt e)`, build `S₃` such that:

* `S₃ = S₂ ∪ S₁`
* `S₂ ⊆ S₃`
* `∀ p ∈ S₃, Truth p` (soundness is preserved)
* `encode_halt e ∈ S₁ ⊆ S₃`
* and `Halts (Machine e)` follows from T1 (canonicity).

**T3 (Strong, one-sided)**: given infinitely many indexed witnesses (an `InfiniteS1` structure),
partition them and construct infinitely many sound extensions `{S₃ₙ}`.

---

## Two-Sided Oracle Variant (Local, One-Step)

Sometimes you want the “choice of side” to be explicit without assuming decidability of `Rev0_K`.
RevHalt provides a **witness-based oracle pick**:

```lean
structure OraclePick (S : ImpossibleSystem Code PropT)
    (encode_halt encode_not_halt : Code → PropT) (e : Code) where
  p : PropT
  cert :
    (Rev0_K S.K (S.Machine e) ∧ p = encode_halt e) ∨
    (¬ Rev0_K S.K (S.Machine e) ∧ p = encode_not_halt e)
```

This is not an `if-then-else`. The branch is carried by `cert`.

Define the one-step extension:

* `S3OneSet S2 pick.p := S2 ∪ {pick.p}`

**T3 (Oracle, local)**: assuming two-sided correctness bridges

* `h_pos : Rev0_K ... → Truth (encode_halt e)`
* `h_neg : ¬Rev0_K ... → Truth (encode_not_halt e)`

the extension `S2 ∪ {pick.p}` is sound, and the theorem returns an explicit branch result tied to halting:

* `(Halts (Machine e) ∧ pick.p = encode_halt e) ∨ (¬Halts (Machine e) ∧ pick.p = encode_not_halt e)`.

This is a “single certified oracle step”, kept local on purpose.

---

## What This Proves (and What It Does Not)

What is proved structurally:

1. **Canonicity (T1)**: valid Kits agree with halting on monotone traces.
2. **Impossibility (T2)**: a system cannot internalize the Kit’s `Rev0_K` predicate.
3. **Complementarity (T3)**: the non-internalizable frontier can be added to any sound base corpus to build larger sound corpora.

What is *not* claimed here:

* No global epistemic impossibility of the form “`S2` cannot decide halting for all programs”.
  Even with the two-sided oracle variant, the framework proves **sound extension + targeted non-internalizability**,
  not a universal decision-theoretic limitation of `S2`.

---

## Build

```bash
lake build
```

---

## Author

Coded with AI assistance under the direction of **John Doe**.

The Lean 4 kernel is the final authority on correctness.
