# RevHalt

RevHalt is a Lean 4 / mathlib development around a “reverse-halting” theory whose goal is to make explicit
where non-constructive strength (EM, choice, etc.) enters: as a **localized access capability** (bridge/pick),
not as an ambient implicit axiom.

## Abstract

RevHalt is an operational metatheory: it treats non-constructive strength (EM, choice, etc.) as an explicit,
localized **access capability** (bridge/pick), and then audits theorem-by-theorem where that capability is used.

The core objects are traces `Trace := ℕ → Prop` and the cumulative closure operator `up`, which turns the
“negative” into an algebraic kernel (`up T = ⊥`) and makes the finite/ω boundary explicit. On top of this, the
project separates formation (R1), semantics (R2), and evaluation/access (R3) via the 3-block architecture
(compile/evaluate/bridge).

From that core, familiar foundational “lenses” show up as derived structure:
- **Ordinal boundary**: the global dichotomy `∀ T, Halts T ∨ Stabilizes T` is exactly EM in logical strength (`dichotomy_all_iff_em`).
- **Scott obstruction**: under Scott-style finite-observation compatibility on a pointed information order, Scott-clopen regions collapse
  (nonempty ⇒ `Set.univ`, proper ⇒ `∅`), so any Scott-compatible observable `α → Bool` is forced to be constant (`scottCompatibleToBool_const`).
- **Diagonal barrier**: the Gödel/Lawvere/Kleene fixed-point pattern is captured as a uniform impossibility theorem (`T2_impossibility`).

All results are machine-verified in Lean 4, with per-theorem axiom audits.

## Documentation

- `docs/overview.md` (framework overview + claim map)

## Core Idea

The project separates three layers that are often conflated:
- **(R1) Formable/testable**: what is encodable and mechanically manipulable.
- **(R2) Semantically true**: what holds in a model (represented externally).
- **(R3) Operationally accessible**: what can be selected/decided by an evaluator/oracle.

The structural core uses traces `Trace := ℕ → Prop` and the cumulative closure operator `up`,
which rigidifies the “negative”: stabilization becomes a **kernel** (`up T = ⊥`) rather than an opaque negation.

## Operational Perspective (R3)

The operational layer is not commentary: it is formalized via an architecture and transfer lemmas.

- **Concrete flow**: `⟨Sat, compile, oBridge⟩` (semantics + compilation + bridge) gives, for an input `(Γ, φ)`:
  1) code `e := compile Γ φ`,
  2) an evaluation predicate `Eval Γ φ := Converges e`,
  3) a mechanical trace `LR Γ φ := aMachine e`,
  4) and, via the bridge, `Eval Γ φ ↔ SemConsequences Sat Γ φ`
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- `Rev0_K K T := K.Proj (up T)` forces a normalization (via `up`) before observation: a decision by access rather than a primitive truth
  (`RevHalt/Base/Kit.lean`).
- `OracleMachine.Eval` is defined solely from compilation (`compile`) and convergence, and `OracleBridge` is the only hypothesis connecting that
  evaluation to semantic consequence (`SemConsequences`) (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- The “Coverage & Decidability” section in `ThreeBlocksArchitecture` proves transfers such as:
  “decidable `Eval` + covering compilation ⇒ decidable `Halts` (and hence decidable `Rev0_K`)”, making explicit where decision power lives.
- T3 formalizes local extensions (a step `S₂ ↦ S₂ ∪ {pick.p}`) from external certificates, and `AbstractDynamics` iterates these steps along a schedule
  and takes a limit (union); `omegaState` captures the canonical state under fairness
  (`RevHalt/Theory/Complementarity.lean`, `RevHalt/Theory/AbstractDynamics.lean`).

## Derived Perspective (Scott)

Scott/domain language is a **derived** way to read RevHalt’s operative core: instead of asking “is `Halts T` true/false?” you ask
“in which **region** (which open set) does `T` lie?”, i.e. what is finitely observable under approximation.

- Put on `Trace` the pointwise order (`T ≤ U` iff `T` implies `U` pointwise), and read “Scott-open” in the standard order-theoretic way:
  `IsScottOpen s := IsUpperSet s ∧ DirSupInacc s` (finitely observable via directed sups).
- `haltsSet_isScottOpen` shows `HaltsSet := {T | Halts T}` is Scott-open (Σ₁), and `stabilizesSet_isScottClosed` shows
  `StabilizesSet := {T | Stabilizes T}` is Scott-closed (Π₁). Moreover, `stabilizesSet_not_isScottOpen` shows the space cannot be “torn apart”.
- Model-independent obstruction: `scottCompatibleToBool_const` shows any Scott-compatible `f : α → Bool` (discrete) is forced to be constant
  on any pointed information order (`OrderBot α`), i.e. it cannot separate a nontrivial predicate. This is the “discrete undecidability” obstruction
  extracted as an invariant of the access/observation interface.
- Specialization: `no_scottOpen_bool_decider_for_stabilizes` rules out any Scott-compatible total decider recognizing `Stabilizes`
  (the `{false}` preimage would have to be Scott-open) (`RevHalt/Theory/ScottTopology.lean`).
- Audit note: the equivalence with `IsOpen`/`IsClosed` for `Topology.WithScott Trace` exists in mathlib but currently uses `Classical.choice`;
  this file keeps the core Scott claims `Classical.choice`-free by avoiding those wrappers.

## What Is Formalized In This Repository

- **Base**: `Trace`, `Halts`, `up` (`RevHalt/Base/Trace.lean`); `RHKit`, `DetectsMonotone`, `Rev0_K` (`RevHalt/Base/Kit.lean`).
- **Structure**: pointwise order on `Trace`, `up` as a closure/reflector, kernel `up_eq_bot_iff`, and “domain/category” structure on `SoundSet`
  (`CompleteLattice`, `SoundChain.lim_eq_sSup_range`, thin categories) (`RevHalt/Theory/Categorical.lean`).
- **Stabilization**: `Stabilizes`, `KitStabilizes`, and equivalences with `up T = ⊥` (`RevHalt/Theory/Stabilization.lean`).
- **Topology (Scott)**: order-theoretic Scott-open/closed (`IsScottOpen`/`IsScottClosed`), `ScottCompatibleToBool`, and the discrete-separation obstruction
  (`RevHalt/Theory/ScottTopology.lean`).
- **T1 (Canonicity)**: `T1_traces` + semantic bridge `T1_semantics` (`RevHalt/Theory/Canonicity.lean`).
- **T2 (Uniform Barrier)**: diagonalization and `T2_impossibility` (`RevHalt/Theory/Impossibility.lean`).
- **T3 (Local Navigation)**: S1/S2/S3 complementarity, `OraclePick`, local extensions and “swap”
  (`RevHalt/Theory/Complementarity.lean`, `RevHalt/Theory/QuantifierSwap.lean`).
- **3-block architecture**: `OracleMachine` + bridge `Eval ↔ SemConsequences`, plus “decidability/coverage” transfers
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- **Abstract dynamics**: `PickWorld`, chains/limits, `omegaState` (`RevHalt/Theory/AbstractDynamics.lean`).
- **Ordinal boundary (EM/LPO)**: characterization `dichotomy_all_iff_em`, plus `LPO`/`LPOBool` and the “const-trick” `AdmitsConst`
  (`RevHalt/Theory/OrdinalBoundary.lean`).
- **Mechanical verification (ordinal boundary)**: “audit / finite stages → ω” with `HaltsUpTo`/`StabilizesUpTo`, `LPOBool ↔ LPOProp`,
  and `stage_zero_is_em` (`RevHalt/Theory/OrdinalMechanical.lean`).
- **Relative foundations**: parameterized principles `EM_Truth` / `EM_Eval`, schemes `LPO_Truth` / `LPO_Eval`, cumulative operator `upE`,
  and kernel/dichotomy characterizations (`RevHalt/Theory/RelativeFoundations.lean`).
- **R1-relative (grammars)**: `LPO_Eval_R1` restricted to an admissible grammar `Adm`, collapse condition `AdmitsConst`, and hierarchy/counterexamples
  (e.g. `CutBit`) (`RevHalt/Theory/RelativeR1.lean`).

## Entry Points

- Library root: `RevHalt.lean` (imports `RevHalt.Main`).
- Base entry: `RevHalt/Base.lean`.
- Theory entry: `RevHalt/Theory.lean`.

## Axiom Audit

Many files end with `#print axioms ...` to audit proofs **theorem-by-theorem**.
Depending on imports and proof style, some results may legitimately mention axioms (e.g. `propext`, `Classical.choice`):
the goal is to **localize** where they enter.

## Choice (AC): Unique vs Construction

In `RevHalt/Theory/RelativeR1.lean` (`CutBit`), we separate explicitly:
- **Uniqueness (Prop)**: `window_unique` + `bit_truth_to_cut_selector_unique` give `∀ n, ∃! k, Window … n x k`.
- **Construction (Type)**: producing `f : ℕ → ℤ` from an existence in `Prop` is a Prop→Type extraction; `bit_truth_to_cut_selector` isolates `Classical.choose`.
- **Constructive-by-search version**: `boundedWindowSelector` builds `f` from `CutDecidable` + a finite bound `cands n` (list search).

## Build

The project depends on mathlib (see `lakefile.lean`). Common commands:

- `lake build`
- `lake build RevHalt`
