# Fixpoint in RevHalt (no latex)

This note defines "fixpoint" as used in RevHalt.

---

## 1) Base definition

Given a transformer F : Set PropT -> Set PropT, a fixpoint is:

```
Fixpoint(F, Γ) := F Γ = Γ
```

This is the only primitive notion. Everything else is a theorem about when a
fixpoint exists under a chosen policy or continuity condition.

---

## 2) Omega-chain fixpoint (TheoryDynamics.lean)

For natural iteration, the omega-limit of a chain is a fixpoint under
omega-continuity:

```
OmegaContinuousSet F ->
F(omegaUnion (iter F Γ0)) = omegaUnion (iter F Γ0)
```

Lemma:
```
omega_fixpoint_of_OmegaContinuousSet
```

---

## 3) Transfinite limit fixpoint (TheoryDynamics_Transfinite.lean)

For ordinal limits, continuity at the limit plus extensivity yields a fixpoint:

```
ContinuousAt F A0 lim + extensivity -> F(Γ_lim) = Γ_lim
```

Lemma:
```
continuous_implies_fixpoint_at_limit
```

---

## 4) LimitOp policy version (TheoryDynamics_Transfinite.lean)

The library also packages "continuity implies fixpoint" as a policy object:

```
FixpointFromContinuity L F A0 lim :=
  ContinuousAtL L F A0 lim ->
  F (transIterL L F A0 lim) = transIterL L F A0 lim
```

Definition:
```
FixpointFromContinuity
```

---

## 5) Jump-limit fixpoint (TheoryDynamics_Transfinite_JumpFixpoint.lean)

For jump limit operators, fixpoints are derived from the jump continuity law:

Lemma:
```
jump_fixpoint_from_continuity
```
