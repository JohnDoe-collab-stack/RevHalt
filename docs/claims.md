# RevHalt: Claims and Scope

This file states the main formal claims and their precise scope.

## Claim A: Structural dichotomy schema

Formal statement:
- A `StructuralDichotomy` provides an operator `O`, a signal predicate `Sig`,
  signal invariance, and a kernel identification `O x = ⊥ ↔ ¬ Sig x`.
- From this, one derives constructive and (classical) equivalences.

Scope:
- Classical logic is needed only for `¬¬ Sig → Sig`.
- The side is not constructed internally; once the side is given, the
  certificate content is forced by `ker_iff` (no additional choice).

Files:
- `RevHalt/Theory/StructuralDichotomy.lean`

## Claim B: T1 (Canonicity)

Formal statement:
- For any kit `K` that detects monotone traces, `Rev0_K K T ↔ Halts T`.

Scope:
- This shows all valid kits agree with standard halting on all traces.

Files:
- `RevHalt/Theory/Canonicity.lean` (theorem `T1_traces`)

## Claim C: T2 (Uniform barrier)

Formal statement:
- No internal predicate can be total + correct + complete + r.e. for all codes.

Scope:
- The diagonal bridge is derived from Kleene SRT. This blocks uniform internal
  decision of halting or stabilization.

Files:
- `RevHalt/Theory/Impossibility.lean` (theorem `T2_impossibility`)

## Claim D: T3 (Complementarity)

Formal statement:
- Given external oracle picks, one can extend a sound corpus by adding the
  chosen sentence, preserving soundness.

Scope:
- This is instancewise: for each `e`, there exists a sound extension deciding
  the chosen side. It does not give a uniform internal predicate.

Files:
- `RevHalt/Theory/Complementarity.lean`

## Claim E: Parametric dynamics

Formal statement:
- For any `PickWorld`, the chain is sound, the limit has a closed form, and
  under fair schedules the limit is schedule-independent.

Scope:
- This is independent of Trace/up. It is a reusable dynamics layer.

Files:
- `RevHalt/Theory/AbstractDynamics.lean`

## Claim F: Ordinal Boundary (NEW)

Formal statement:
```lean
theorem dichotomy_all_iff_em :
    (∀ T : Trace, Halts T ∨ Stabilizes T) ↔ (∀ P : Prop, P ∨ ¬ P)
```

Scope:
- **Dichotomy = EM exactly** (verified by `#print axioms`: zero axioms)
- All structure theorems are constructive (0 axioms)
- EM as hypothesis suffices (no Classical.choice needed axiomatically)
- The constructive/classical frontier = finite/ω ordinal frontier

Files:
- `RevHalt/Theory/OrdinalBoundary.lean`

## Non-claims / open directions

- P vs NP is not formalized; it is a conceptual direction in `TODO/PvsNP.md`.
- The oracle that provides the side is external; the formalism does not build
  it internally.
