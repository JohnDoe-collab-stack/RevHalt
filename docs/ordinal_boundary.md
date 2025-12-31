# The Classical Boundary as Ordinal Completion

## Thesis

The constructive/classical frontier in RevHalt **is** the finite/limit ordinal frontier.

- **Constructive** = work at finite ordinals (accumulation)
- **Classical** = passage to limit ordinal ω (completion)
- **EM** (`¬¬P → P`) = the ordinal completion operator

---

## What Constructive Logic Builds

All of this is proven **without** `classical`:

| Object | Status | File Reference |
|--------|--------|----------------|
| `up : Trace → Trace` | Defined | `StructuralDichotomy.lean` |
| `up` idempotent | Proved | `up_idem` |
| `up` monotone | Proved | `up_mono` |
| `ker_iff` : `up T = ⊥ ↔ ∀n. ¬T n` | Proved | `up_eq_bot_iff` |
| `sig_invar` : `Halts (up T) ↔ Halts T` | Proved | `exists_up_iff` |
| Dichotomy exclusive | Proved | `dichotomy_exclusive` |
| `¬¬(Sig x ∨ ¬Sig x)` | Trivially true | Logic |
| Chain construction | Defined | `AbstractDynamics.lean` |
| Chain monotonicity | Proved | `chain_mono` |
| Chain soundness | Proved | `chain_sound` |

The constructive fragment builds **the entire structure**.

---

## What Constructive Logic Cannot Do

Pass from `¬¬(P ∨ ¬P)` to `P ∨ ¬P`.

Affirm which side holds **for a given x**.

This is the **only** gap. Everything else is constructive.

---

## The Ordinal Interpretation

### Σ₁ (∃n. T n) — Finite Ordinals

- Verifiable by finding a witness at some finite stage
- Constructively affirmable: produce n, verify T n

### Π₁ (∀n. ¬T n) — Limit Ordinal ω

- Affirmable only after checking all finite stages
- Requires passage to the limit

### The Pattern

| Formula | Ordinal | Constructive? |
|---------|---------|---------------|
| `∃n. T n` | α < ω | ✅ Yes |
| `∀n. ¬T n` | ω | ❌ Requires EM |
| Verification step n | n | ✅ Yes |
| Limit/completion | ω | ❌ Requires EM |

---

## EM as Ordinal Completion

`¬¬P → P` says: "The accumulation is complete, therefore the limit fact holds."

This is exactly **passage to ω**:
- You've verified something holds at every finite stage (constructive work)
- You conclude it holds at the limit (classical completion)

### In RevHalt's Code

```lean
-- Constructive: builds the double negation
theorem ne_bot_imp_notnot_sig (x : X) : D.O x ≠ ⊥ → ¬¬ D.Sig x

-- Classical: completes to the limit (EM HERE)
theorem ne_bot_imp_sig (x : X) : D.O x ≠ ⊥ → D.Sig x := by
  classical  -- ← ordinal completion
  intro hne
  exact Classical.not_not.mp (D.ne_bot_imp_notnot_sig x hne)
```

The `classical` tactic is the **ω-operator**.

---

## The Evaluative Boundary

### Reading vs Constructing

| Operation | Ordinal Level | Logic |
|-----------|---------------|-------|
| Build `up T` | Finite | Constructive |
| Prove structure theorems | Finite | Constructive |
| Construct the chain | Finite stages | Constructive |
| **Read which side** | ω | Classical |

The classical logic is needed exactly at the **evaluation point**.

You can build arbitrarily complex structures constructively.
You need EM only to **read the answer** for a specific input.

---

## Why This Matters

### Before This Analysis

"Classical logic is needed somewhere in RevHalt."

### After This Analysis

- **Where**: Exactly at `¬¬P → P`, one theorem
- **Why**: It's the ordinal completion operator
- **What it does**: Evaluates the limit of a constructive accumulation

Classical logic is not a crutch. It is **ordinal ω made logical**.

---

## Proof Map

| Theorem | Classical? | What It Does |
|---------|------------|--------------|
| `sig_imp_ne_bot` | ❌ No | Finite verification |
| `ne_bot_imp_notnot_sig` | ❌ No | Finite accumulation |
| `bot_imp_not_sig` | ❌ No | Finite verification |
| `not_sig_imp_bot` | ❌ No | Finite verification |
| `ne_bot_imp_sig` | ✅ Yes | **ω-completion** |
| `sig_iff_ne_bot` | ✅ Yes | Uses `ne_bot_imp_sig` |
| `dichotomy` | ✅ Yes | Uses EM |
| `dichotomy_exclusive` | ❌ No | Finite |

---

## The Formula

```
Constructive = ℕ-indexed work
Classical = passage to ω
EM = lim_{n→ω}
```

This is not metaphor. This is what the code shows.
