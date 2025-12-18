# RevHalt

A Lean 4 framework that **inverts** the perspective on incompleteness.

**Classical approach**: Start from a model (ℕ), observe that some truths escape proof.

**RevHalt**: Start from an **abstract observation instrument** (the Kit), prove that no logical system can internalize what this instrument sees, then **structure the gap** as exploitable content.

---

## The Inversion

| Aspect | Classical (Gödel/Turing) | RevHalt |
|--------|--------------------------|---------|
| Source of truth | Standard model (ℕ, Turing) | Abstract Kit (`RHKit`) |
| What escapes | Truths of ℕ | Kit-certified verdicts |
| The gap | Abstract existence | **Typed set** `S₁` |
| After incompleteness | Ad hoc extension | **Complementarity** (S₃ = S₁ ∪ S₂) |

---

## Core Files

```
RevHalt/Base/Trace.lean      # Trace := ℕ → Prop, Halts, up
RevHalt/Base/Kit.lean        # RHKit, DetectsMonotone, Rev0_K
RevHalt/Theory/Canonicity.lean    # T1: Rev0_K ↔ Halts
RevHalt/Theory/Impossibility.lean # T2: No internal predicate captures Rev0_K
RevHalt/Theory/Complementarity.lean # T3: S₁ ∪ S₂ = S₃ is sound
```

---

## The Kit

```lean
structure RHKit where
  Proj : Trace → Prop

def DetectsMonotone (K : RHKit) : Prop :=
  ∀ X : Trace, Monotone X → (K.Proj X ↔ ∃ n, X n)

def Rev0_K (K : RHKit) (T : Trace) : Prop :=
  K.Proj (up T)
```

The Kit is an **abstract observation mechanism**. The only requirement is `DetectsMonotone`: on monotone traces, the Kit agrees with standard existence.

**T1 (Canonicity)**: `Rev0_K K T ↔ Halts T` for any valid Kit K.

→ All valid Kits see the same thing. The Kit **defines** computational truth.

---

## The Impossibility

```lean
structure ImpossibleSystem (Code PropT : Type) where
  Machine : Code → Trace       -- Physical layer
  K : RHKit                    -- Observation instrument
  h_canon : DetectsMonotone K  -- Kit is valid (T1 applies)
  Provable : PropT → Prop      -- Logical layer
  diagonal_program : ...       -- Bridge to Rev0_K
```

**T2**: No `InternalHaltingPredicate` exists for a canonical `ImpossibleSystem`.

→ The system cannot internalize what the Kit sees. Not because "some truths escape" — because **this specific instrument's verdicts** cannot be captured.

---

## The Gap (S₁)

```lean
def S1Set (S : ImpossibleSystem Code PropT) (encode_halt : Code → PropT) : Set PropT :=
  { p | ∃ e, p = encode_halt e ∧ Rev0_K S.K (S.Machine e) ∧ ¬ S.Provable (encode_halt e) }
```

S₁ is **typed explicitly**:
- `Rev0_K S.K (S.Machine e)` — the Kit certifies halting
- `¬ S.Provable (encode_halt e)` — the system can't prove it

This is not "some true unprovable statement exists". This is **exactly what the gap is made of**.

---

## Complementarity (S₃ = S₁ ∪ S₂)

**T3 (Weak)**: Given a witness `(e, hKit, hUnprov)`:
- Construct `S₃ := S₂ ∪ S₁`
- S₃ is **sound** (every element is true)
- `encode_halt e ∈ S₁ ⊆ S₃`
- `Halts (Machine e)` via T1

**T3 (Strong)**: Given infinitely many S₁ elements:
- Partition them into disjoint families
- Construct infinitely many sound extensions {S₃ₙ}

→ The gap is not an obstacle. It is **exploitable structure**.

---

## InfiniteS1 — Indexed Witnesses

```lean
structure InfiniteS1 (Code PropT : Type) (S : ImpossibleSystem Code PropT)
    (encode_halt : Code → PropT) where
  Index : Type
  InfiniteIndex : Infinite Index
  family : Index → Code
  distinct : Function.Injective family
  kit : ∀ i, Rev0_K S.K (S.Machine (family i))
  unprovable : ∀ i, ¬ S.Provable (encode_halt (family i))
```

No added hypotheses (no `Injective encode_halt`). The witnesses are primitive; S1Set membership is **derived**.

---

## What This Proves

1. **Canonicity**: Computational truth is objective (Kit-independent on monotone traces)
2. **Impossibility**: The Kit's verdicts cannot be internalized
3. **Complementarity**: The non-internalizable truths (S₁) can be added to any sound base (S₂) to form a larger sound theory (S₃)

This is not a restatement of Gödel. It is a **structural decomposition** of incompleteness into typed, exploitable components.

---

## Build

```bash
lake build
```

---

## Author

Coded with AI assistance under the direction of **John Doe**.

The Lean 4 kernel is the final authority on correctness.
