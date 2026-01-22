# RevHalt: Cycle from A to Z (no LaTeX)

This note explains, end-to-end, how to get a strict repeating “cycle of horns” using:

- the trilemma (`RevHalt/Trilemma/Trilemma.lean`)
- the spiral facts (`RevHalt/Trilemma/Spiral.lean`)
- the cycle clock (`RevHalt/Trilemma/Cycle.lean`)
- complementarity S1/S2/S3 (`RevHalt/Theory/Complementarity.lean`)

It is written in plain Markdown, no LaTeX. Identifiers and file paths are in backticks.

---

## A) The split: syntax vs semantics

We work with two dissociated layers:

1) **S1 = my framework (syntax/frontier)**  
   This is the internal RevHalt layer: it defines the dynamics, the frontier, and the structural theorems.

2) **S2 = Peano (semantics/arithmetic)**  
   This is an external evaluator/producer. It is allowed to carry extra “values”, indexed by the natural number `n`.

3) **S3 = the solution = union**  
   S3 is the combination “keep S2 and add S1”, i.e. “semantics plus frontier injections”.

This is exactly the “complementarity” pattern of `S1`, `S2`, `S3`:

- `S1` is the frontier set of sentences (kit-certified but not provable internally).
- `S2` is an externally sound base corpus (think: Peano).
- `S3` is the combined corpus `S2 ∪ S1`.

In the code:

- `S1Set` and `S3Set` are defined in `RevHalt/Theory/Complementarity.lean`.
- `S3Set S S2 encode_halt = S2 ∪ S1Set S encode_halt`.

Important: on the RevHalt side we do not need “values”. RevHalt provides structure and implications. Values can live entirely on the S2 (arithmetic) side and be injected at the frontier.

---

## B) The trilemma: three horns, one must fail

RevHalt exposes three properties (informally “horns”):

- `Absorbable` (stability/absorption at a finite stage)
- `OmegaAdmissible` (a “good” omega-limit: fixed point + prov-closed)
- `RouteIIAt` (frontier nonempty at the omega-limit)

The trilemma states you cannot have all three simultaneously.

In the code, the packaged versions are in:

- `RevHalt/Trilemma/Trilemma.lean`

The file gives:

1) A conjunction form:

- `trilemma_not_all` (and the step-indexed version `trilemma_not_all_at_step`)

2) The three “two imply not third” corollaries:

- `absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega`  
  (A and B imply not C)
- `absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega`  
  (A and C imply not B)
- `omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step`  
  (B and C imply not A)

This “two imply not third” interface is the engine used by the cycle: if you can realize two desiderata at some chosen time, the trilemma forces the third horn to fail.

---

## C) The spiral: strict growth when frontier regenerates

The spiral is a separate ingredient: it provides strict growth of the trajectory when the correct hypotheses hold.

In the code, see:

- `RevHalt/Trilemma/Spiral.lean`

Key ideas:

- A trajectory is a spiral if it strictly grows at each step: `IsSpiral Γ := for all n, Γ n ⊂ Γ (n+1)`.
- If a frontier witness exists at each step (regeneration), and `PostSplitter` propagates, you can prove strict growth of the canonical trajectory.

You can read this as: “if the frontier keeps providing new certified information, then the theory chain cannot stagnate; it must strictly extend forever”.

This gives the “spiral” part of the story: growth is structurally forced under regeneration.

---

## D) Complementarity: S1, S2, S3 in code form

In `RevHalt/Theory/Complementarity.lean`:

- `S1Set` is the one-sided frontier: sentences of the form `encode_halt e` such that the kit certifies, and the system cannot prove it.
- `S3Set` is literally `S2 ∪ S1Set`.

The file also provides the key pattern for “semantics chooses without internal decidability”:

- `OraclePick` packages a chosen sentence together with a certificate of the branch (a `PSum`).
- `T3_oracle_extension_explicit` shows you can extend a sound base `S2` by adding exactly `pick.p` and keep soundness.

Crucial point: the branch is carried by the external certificate (`pick.cert`), not computed by internal case-splitting. This matches the “S2 controls an index/value, S1 consumes it” worldview.

---

## E) The cycle goal: strict repeating horns

We want a strict repeating pattern of horns like:

- phase 0: realize `B` and `C`, so horn “not A” is forced
- phase 1: realize `A` and `C`, so horn “not B” is forced
- phase 2: realize `A` and `B`, so horn “not C” is forced
- and then repeat

This is not “the trilemma alone”. This is: trilemma plus an external schedule that tells you, at which indices `n`, which pair is realized.

In the code, the cycle construction is in:

- `RevHalt/Trilemma/Cycle.lean`

---

## F) Cycle.lean: what it defines

`RevHalt/Trilemma/Cycle.lean` defines:

### F1) The three predicates at an index

- `A hIdem hProvCn n` means `Absorbable` at stage `n+1` of `chainState`.
- `B hIdem hProvCn n` means `OmegaAdmissible` for the omega-limit built from stage `n`.
- `C hIdem hProvCn n` means `RouteIIAt` for that same omega-limit.

### F2) A notion of “cofinal availability”

- `Cofinal P` means: for all `N`, there exists `n ≥ N` such that `P n`.
- `CofinalWitness P` is the constructive witness type: given `N`, you return an explicit `n` with a proof that `n ≥ N` and `P n`.

This is the key: a witness is data indexed by `N`, i.e. an “arithmetical function of N”.

### F3) Modes and required pairs

`CycleMode` is a 3-way mode:

- `BC`, `AC`, `AB`

`cycleMode k` is periodic:

- `k % 3 = 0` gives `BC`
- `k % 3 = 1` gives `AC`
- otherwise gives `AB`

`Pair mode n` is the proposition “the required pair holds at index n”:

- `Pair BC n` is `B n ∧ C n`
- `Pair AC n` is `A n ∧ C n`
- `Pair AB n` is `A n ∧ B n`

### F4) The clock: `cycleTimes`

`cycleTimes` is a function `Nat → Nat` that constructs a strictly increasing subsequence:

- `cycleTimes 0` picks a witness time for `Pair (cycleMode 0)` at threshold `0`.
- `cycleTimes (k+1)` picks a witness time for `Pair (cycleMode (k+1))` at threshold `cycleTimes k + 1`.

This is how you get “hitting times” without any classical search:
you do not search, you use the witness functions provided by the semantics (as data).

There are two theorems:

- `cycleTimes_spec` says: the required pair holds at time `cycleTimes k`.
- `cycleTimes_strictMono` says: `cycleTimes k < cycleTimes (k+1)`.

### F5) Forcing the horn: `strict_cycle_horns`

Finally, `strict_cycle_horns` uses the trilemma “two imply not third” lemmas:

- in mode `BC`, from `B ∧ C` it concludes `¬A`
- in mode `AC`, from `A ∧ C` it concludes `¬B`
- in mode `AB`, from `A ∧ B` it concludes `¬C`

So: if you can supply witnesses that realize the pairs according to the mode schedule, the cycle of horns is forced.

This is the precise sense in which “we obtain the cycle”.

---

## G) Where do the witnesses come from?

This is the key design choice of your framework:

- RevHalt (S1) does not need to “compute” the witnesses.
- Arithmetic (S2) can provide them as a function of the index.
- The frontier is where these are injected.

In terms of the code, that means:

- you do not try to decide `A/B/C` inside RevHalt
- you pass `CofinalWitness` values to `cycleTimes` and `strict_cycle_horns`

This matches the “complementarity/oracle pick” style: the external layer provides a certificate, the internal layer verifies implications.

### G1) A concrete derived witness already in Cycle.lean

`Cycle.lean` also contains one useful derived witness for the `BC` pair:

- `witBC_of_continuity_and_routeII`

It shows that if you assume:

- omega-limit continuity properties (`ProvClosedDirected`, `CnOmegaContinuous`, plus `CnExtensive`, `CnIdem`, `ProvClosedCn`)
- and Route II style assumptions (`Soundness` uniform, `NegativeComplete`, `Barrier`)

then you can construct a `CofinalWitness` for `B n ∧ C n` (in fact, “for all n”).

This is an example of how “semantics-side axioms” can manufacture the schedule-data that the cycle consumes.

---

## H) How this uses everything (summary)

Putting it together, the “A to Z” story is:

1) `S1` (your framework) provides the internal dynamics and the frontier notion.
2) `S2` (Peano/arithmetic semantics) provides index-driven data: schedules, witnesses, certificates.
3) Complementarity says: the combined object is `S3 = S2 ∪ S1`.
4) The spiral says: under regeneration, the internal trajectory strictly grows.
5) The trilemma says: you cannot have `A ∧ B ∧ C`, and “two imply not third”.
6) The cycle says: if arithmetic provides witness functions that realize pairs by phase, then at the “cycle times” the missing horn is forced in strict periodic order.

This is exactly the “verify without proving in the framework” posture:
RevHalt proves conditional structural implications; arithmetic supplies the values indexed by `n`.

---

## I) File pointers

- Trilemma (horn incompatibility): `RevHalt/Trilemma/Trilemma.lean`
- Spiral (strict growth): `RevHalt/Trilemma/Spiral.lean`
- Cycle clock and horns: `RevHalt/Trilemma/Cycle.lean`
- Complementarity S1/S2/S3 and oracle pick: `RevHalt/Theory/Complementarity.lean`
- Conservation (MissingFrom vs frontier under Absorbable): `RevHalt/Theory/TheoryDynamics.lean` (search `missing_F0_eq_S1_of_absorbable`)

