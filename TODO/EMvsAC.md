# TODO: EM vs AC Clarification

## Status: ✅ PROVEN

The claim "Dichotomy is EM-regime, not AC-regime" is now **formally verified**.

---

## What Is Proven (in `OrdinalBoundary.lean`)

### 1. Structure is axiom-free
```lean
#print axioms up_idem_iff           -- does not depend on any axioms
#print axioms dichotomy_exclusive   -- does not depend on any axioms
#print axioms dichotomy_double_neg  -- does not depend on any axioms
```

### 2. EM as hypothesis → Dichotomy (0 axioms)
```lean
theorem dichotomy_from_em (em : ∀ P, P ∨ ¬P) (T : Trace) :
    Halts T ∨ Stabilizes T
-- #print axioms: does not depend on any axioms
```

### 3. Dichotomy → EM (0 axioms)
```lean
theorem em_of_dichotomy_all (dich : ∀ T, Halts T ∨ Stabilizes T) :
    ∀ P, P ∨ ¬ P
-- #print axioms: does not depend on any axioms
```

### 4. The exact equivalence
```lean
theorem dichotomy_all_iff_em :
    (∀ T, Halts T ∨ Stabilizes T) ↔ (∀ P, P ∨ ¬ P)
-- #print axioms: does not depend on any axioms
```

---

## Conclusion

**Dichotomy = EM, exactly. Verified by Lean.**

- The dichotomy is **exactly** EM in logical strength
- No AC needed (the "choice" is binary and forced)
- EM is the only non-constructive ingredient

---

## Technical Note

When using Lean's `classical` tactic + `by_cases`:
```lean
theorem dichotomy (T : Trace) : Halts T ∨ Stabilizes T := by
  classical
  by_cases h : Halts T ...
-- #print axioms: depends on Classical.choice
```

This is because Lean routes `by_cases` through `propDecidable` which uses `Classical.choice`. 

However, when EM is given as a **hypothesis**:
```lean
theorem dichotomy_from_em (em : ∀ P, P ∨ ¬P) ...
-- #print axioms: does not depend on any axioms
```

This shows the distinction is real: EM suffices, the rest is Lean implementation.

---

## Files

- `OrdinalBoundary.lean` — all proofs
- `StructuralDichotomy.lean` — abstract schema
