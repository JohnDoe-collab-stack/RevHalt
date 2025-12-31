# The Classical Boundary as Ordinal Completion

## Thesis (PROVEN)

The constructive/classical frontier **is** the finite/limit ordinal frontier.

**Formally verified in Lean** (`OrdinalBoundary.lean`):
- **Constructive = 0 axioms** (pure logic + definitions)
- **Classical = Classical.choice** (via Lean's routing)
- **EM as hypothesis = 0 axioms** (the exact characterization)

---

## The Main Theorem

```lean
theorem dichotomy_all_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬ P)
```

**Dichotomy ↔ EM exactly.** Zero axioms.

---

## Axiom Analysis (machine-verified)

### Constructive (0 axioms)

| Theorem | Axioms |
|---------|--------|
| `up_idem_iff` | none |
| `up_mono` | none |
| `halts_up_iff` | none |
| `stabilizes_iff_forall_not_up` | none |
| `stabilizes_iff_not_halts` | none |
| `dichotomy_exclusive` | none |
| `dichotomy_double_neg` | none |
| `not_stabilizes_imp_notnot_halts` | none |
| `dichotomy_from_em` | none |
| `dichotomy_all_iff_em` | none |

### Classical (via Lean)

| Theorem | Axioms |
|---------|--------|
| `dichotomy` | propext, Classical.choice, Quot.sound |
| `not_stabilizes_imp_halts` | propext, Classical.choice, Quot.sound |

---

## The Ordinal Interpretation

| Fragment | Axioms | = Ordinal |
|----------|--------|-----------|
| Structure (up, mono, etc.) | 0 | Finite |
| `¬¬(Halts ∨ Stab)` | 0 | Limit from below |
| `Halts ∨ Stab` (EM hyp) | 0 | ω (EM explicit) |
| `Halts ∨ Stab` (classical) | Choice | ω (Lean route) |

---

## Key Insight

`¬¬P → P` = passage to ω.

- Constructive: accumulate at all finite ordinals
- Classical: affirm the limit

The `classical` tactic is the **ω-operator**.

---

## Files

- `OrdinalBoundary.lean` — formal proofs
- `StructuralDichotomy.lean` — abstract schema

---

## Conclusion

> The dichotomy Halts/Stabilizes is **exactly** EM in logical strength.
> 
> No more, no less. Verified by Lean.
