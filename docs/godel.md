# Toward Gödel in RevHalt

RevHalt already contains the *structural core* of Gödel-style arguments: a **diagonal barrier**
showing that certain “total + correct + complete” internalizations are impossible.

What remains is not “adding Gödel as folklore”, but making explicit which *interfaces* must be present
to recover the classical incompleteness theorems as instances.

## 1) What we already have (the diagonal barrier)

`RevHalt/Theory/Impossibility.lean` proves:

- `RevHalt.T2_impossibility`

Informal reading:

> No internally defined predicate can be simultaneously:
> - total (decides every case),
> - correct/complete w.r.t. the external semantics of `Rev0_K`,
> - and compatible with an r.e. (semi-decidable) notion of refutability.

The proof is a fixed-point/diagonal argument (Kleene SRT via `Nat.Partrec.Code.fixed_point₂`)
packaged through the RevHalt interface (`Trace`, `Machine`, `Rev0_K`, and the kit hypotheses).

This is “Gödel/Lawvere” in operational clothes: it forbids a certain kind of *self-contained*
decision/verification layer from fully internalizing a semantics it does not control.

## 2) How this relates to Gödel (what you still need to instantiate)

Classical Gödel (First Incompleteness) is about an arithmetic theory `T` and a sentence `G` such that,
assuming consistency (and typically effective axiomatizability), `T` cannot decide `G`.

To recover that shape inside RevHalt, you need an explicit *syntax/proof* interface:

1. **A sentence type** (or codes) `PropT` (Gödel numbers / formulas).
2. **A provability predicate** `Provable : PropT → Prop` which is r.e. (or has a semi-decider).
3. **Negation/falsehood** `Not : PropT → PropT`, `FalseT : PropT`, and minimal consistency infrastructure.
4. **A diagonal/fixed-point principle at the syntax level**:
   something that produces a “self-referential” `G` for a given schema (Lawvere-style).

RevHalt already provides (4) in a *computability-coded* form (fixed points over `Nat.Partrec.Code`),
and (3) abstractly as `ImpossibleSystem` inside `Impossibility.lean`.

What is still missing for “full Gödel” is an explicit instantiation where:

- `PropT` genuinely represents *arithmetical sentences*,
- `Provable` is the provability predicate of a concrete theory,
- and the diagonal/fixed-point is shown to match the arithmetical diagonal lemma.

## 3) A pragmatic implementation path (incremental)

### Step A — “Gödel lens” without arithmetic

Implemented in `RevHalt/Theory/GodelLens.lean`:

- `RevHalt.not_total_of_correct_complete_semidec` (no witness extraction; axiom audit currently inherits `Classical.choice` from `PartrecCode`)
- `RevHalt.exists_undecidable_classical_of_correct_complete_semidec` (classical: extracts a specific undecidable `e`)
- `RevHalt.exists_true_unprovable_classical_of_correct_complete_semidec` (classical: with an external `Truth` semantics and `Truth(Not p) ↔ ¬Truth p`,
  produces a “true but unprovable” sentence)

In addition, for **Gödel I in the standard “true-but-unprovable” shape**, the file now includes:

- `RevHalt.exists_nonhalting_unprovable_neg_of_correct_semidec` (constructive existential: builds a specific `e` with `¬Rev0_K …` and `¬Provable (¬H e)`
  from *consistency + positive correctness + r.e. refutability*; no completeness hypothesis)
- `RevHalt.godelI_exists_true_unprovable_of_correct_semidec` (semantic wrapper: given `Truth` interpreting `H` as halting and respecting negation,
  returns `∃ p, Truth p ∧ ¬Provable p`)

This stays in the RevHalt style: the interface is primary, classical extraction is isolated, and proofs are audited.

### Step A' — A single “Gödel I standard” interface (packaging)

`RevHalt/Theory/GodelIStandard.lean` bundles exactly the assumptions needed to instantiate the standard
“true but unprovable” conclusion, and then exports:

- `RevHalt.GodelIStandard.exists_nonhalting_unprovable_neg`
- `RevHalt.GodelIStandard.exists_true_unprovable`

### Step B — Instantiate on halting / r.e. predicates (already close)

Show, as explicit corollaries, that any consistent internal system attempting to decide
`Rev0_K`-semantics over the `Machine` model cannot be both complete and total.

This is already essentially what `T2_impossibility` says; the value is presentation + reuse.

### Step C — Arithmetic instantiation (bigger project)

If you want Gödel in the classical sense (PA/Q/etc.), you will need:

- a formal language of arithmetic,
- a proof system and provability predicate,
- representability of primitive recursive relations (enough to talk about proofs),
- the diagonal lemma (syntactic fixed point),
- and a consistency/soundness assumption to conclude “true but unprovable”.

This is doable, but it is a new module-scale effort.

## 4) Claim map (current state)

- Diagonal barrier / fixed point packaged: `RevHalt.T2_impossibility` (`RevHalt/Theory/Impossibility.lean`)
- Gödel lens (interface → incompleteness-shaped corollaries): `RevHalt.not_total_of_correct_complete_semidec`,
  `RevHalt.exists_undecidable_classical_of_correct_complete_semidec`,
  `RevHalt.exists_true_unprovable_classical_of_correct_complete_semidec` (`RevHalt/Theory/GodelLens.lean`)
- Scott-style “no discrete separation” obstruction (derived lens): `RevHalt.scottCompatibleToBool_const` (`RevHalt/Theory/ScottTopology.lean`)
- Exact EM boundary for global dichotomy: `RevHalt.OrdinalBoundary.dichotomy_all_iff_em` (`RevHalt/Theory/OrdinalBoundary.lean`)

These three are complementary:

- **Gödel**: diagonal obstruction (internalization barrier).
- **Turing**: discrete separation obstruction (finite observation cannot decide limits).
- **Ordinal/EM**: completion barrier (finite → ω is exactly `¬¬P → P` / EM strength).

RevHalt’s contribution is that they are all expressed as outputs of an explicit access interface,
not as ambient metatheory.
