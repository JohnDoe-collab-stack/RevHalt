# Toward Gödel in RevHalt

RevHalt already contains the *structural core* of Gödel-style arguments: a **diagonal barrier**
showing that certain “total + correct + complete” internalizations are impossible.

What remains is not “adding Gödel as folklore”, but making explicit which *interfaces* must be present
to recover the classical incompleteness theorems as instances.

## 1) What we already have (the diagonal barrier)

`RevHalt/Theory/Impossibility.lean` proves:

- `RevHalt.T2_impossibility`
- `RevHalt.diagonal_bridge_re` (a convenience wrapper bundling r.e. hypotheses)

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

As of now, the “sentence type + standard-model truth” part is also fixed:

- `RevHalt/Theory/ArithmeticLanguage.lean` defines a minimal first-order arithmetic language (`0`, `succ`, `+`, `*`),
  its standard structure on `ℕ`, and `Truth : Sentence → Prop` as satisfaction in `ℕ`.
- `RevHalt/Theory/ArithmeticEncoding.lean` equips the arithmetic syntax (`Sentence`) with `Encodable` (via mathlib’s list encodings),
  which is a prerequisite for any r.e. (proof-checking / enumeration) approach to Gödel classical.
- `RevHalt/Theory/ArithmeticProvability.lean` turns a provability predicate on arithmetic sentences into an
  `ImpossibleSystem` (using syntactic `⊥` and `p.not`).
- `RevHalt/Theory/RobinsonQ.lean` defines Robinson arithmetic `Q` as a concrete finite theory object (`QTheory`)
  and proves semantic soundness in the standard model (`nat_models_QTheory : (ℕ : Type) ⊨ QTheory`).

What remains to get *full* “Gödel classical” is the PA/Q instantiation of `Provable` and the computation-to-arithmetic bridge (`H` below).

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

**r.e. packaging note.**
Many lemmas come in two equivalent forms:
- a “raw” form with explicit `f`, `f_partrec`, `semidec`,
- and a “bundled” form using `RECodePred` (`RevHalt/Theory/RECodePred.lean`), e.g.
  `exists_nonhalting_unprovable_neg_of_correct_re` / `godelI_exists_true_unprovable_of_correct_re`.
This keeps the diagonal/Gödel interface clean and reusable.

### Step A' — A single “Gödel I standard” interface (packaging)

`RevHalt/Theory/GodelIStandard.lean` bundles exactly the assumptions needed to instantiate the standard
“true but unprovable” conclusion, and then exports:

- `RevHalt.GodelIStandard.exists_nonhalting_unprovable_neg`
- `RevHalt.GodelIStandard.exists_true_unprovable`

It also exposes the r.e. refutability field as a reusable object:

- `RevHalt.GodelIStandard.reNotH : RECodePred (fun c => Provable (¬H c))`

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

RevHalt now provides an explicit staging point for it:

- `RevHalt/Theory/GodelIArithmetic.lean` packages exactly the remaining obligations as an interface
  (`RevHalt.Arithmetic.GodelIArith`) and then produces:
  - `RevHalt.Arithmetic.GodelIArith.exists_nonhalting_unprovable_notH`
  - `RevHalt.Arithmetic.GodelIArith.exists_true_unprovable`

In other words: once you supply the PA/Q proof predicate and the arithmetization of halting (`H`), the “true in ℕ but not provable” output is automatic.

## 3.5) Exhaustive “Gödel I standard” implementation checklist (PA/Q target)

This is the complete list of remaining technical work to turn the current “Gödel lens” into a
fully classical instantiation (PA or Q, standard-model truth, proof-theoretic provability).

## 3.5.1) What mathlib already gives you (useful building blocks)

If you decide to push “Gödel classical” all the way down to arithmetic syntax, it helps to know what
already exists in mathlib today (so you can reuse it rather than rebuilding from scratch):

- **First-order syntax encodings**: `Mathlib.ModelTheory.Encoding` defines list-based encodings for
  `FirstOrder.Language.Term` and `FirstOrder.Language.BoundedFormula`. It already provides `Encodable`
  instances, and explicitly notes the next missing layer (“Primcodable instances … computability facts …”)
  that you will likely need for a full incompleteness proof.
- **RevHalt countability / `Primcodable` for arithmetic sentences**: `RevHalt/Theory/ArithmeticNumerals.lean`
  gives an explicit injection `ℕ → Sentence`, hence `Infinite Sentence`, and then installs
  `Denumerable Sentence` and `Primcodable Sentence`. This unlocks r.e. / partial-recursive interfaces
  over `Sentence` without waiting on upstream `Primcodable` instances for all first-order syntax.
- **`REPred` → `RECodePred` glue**: `RevHalt/Theory/RECodePredExtras.lean` provides
  `RevHalt.RECodePred.of_REPred_comp`, which turns an r.e. predicate `REPred P` on a `Primcodable` type
  into the exact `RECodePred (fun c => P (g c))` hypothesis used by the Gödel interfaces, given a
  computable map `g : Nat.Partrec.Code → α`.
- **Gödel’s β-function lemma**: `Mathlib.Logic.Godel.GodelBetaFunction` proves the β-function lemma,
  the standard way to arithmetize finite sequences inside arithmetic.
- **Partial recursive codes**: `Mathlib.Computability.PartrecCode` (which RevHalt already uses) gives
  a concrete code model (`Nat.Partrec.Code`) and fixed-point machinery (`fixed_point₂`).

What mathlib does *not* currently provide “out of the box” is a full **syntactic proof system** for
first-order theories (a derivability relation with an r.e. proof checker) in the same style as the
semantics layer. That is why RevHalt keeps provability as an explicit interface.

### (C1) Proof system / provability predicate (syntax → `Prop`)

Goal: define `Provable_T : Sentence → Prop` for a concrete arithmetic theory `T` (Q or PA).

What you need:
- a concrete proof object type (typically encoded as `Nat` / `List Nat`),
- a decidable checker `IsProof_T : Proof → Sentence → Prop` (or a computable relation),
- define `Provable_T φ := ∃ π, IsProof_T π φ`,
- then package it as `RevHalt.Arithmetic.ProvabilitySystem` (`RevHalt/Theory/ArithmeticProvability.lean`).

Minimum properties to supply (already required by `ProvabilitySystem`):
- `consistent : ¬ Provable_T ⊥`
- `absurd : Provable_T φ → Provable_T (¬φ) → Provable_T ⊥`

Baseline (already implemented): `RevHalt.Arithmetic.QProvabilitySystemSem` in
`RevHalt/Theory/RobinsonQProvability.lean` packages **semantic consequence** (`QTheory ⊨ᵇ φ`) as a
`ProvabilitySystem`. This is a useful C1 sanity-check, but it is **not** the r.e. syntactic provability
needed for full Gödel classical.

### (C2) Theory object (already present for Q)

Robinson arithmetic as an axiom set already exists:
- `RevHalt.Arithmetic.QTheory` (`RevHalt/Theory/RobinsonQ.lean`)
- and semantic soundness in the standard model:
  `RevHalt.Arithmetic.nat_models_QTheory : (ℕ : Type) ⊨ QTheory`

If you build `Provable_T` for Q/PA, you will also typically want:
- “axioms are provable”: `φ ∈ T → Provable_T φ`
- “rules preserve truth”: soundness `Provable_T φ → Truth φ` (optional but standard to derive consistency from a model)

### (C3) Arithmetize halting: `H : Code → Sentence`

Goal: define `H e` as a Σ₁ arithmetic sentence expressing “the program `e` halts”.

In RevHalt terms, you need:
- `H : Code → Sentence`
- `truth_H : ∀ e, Truth (H e) ↔ Rev0_K K (Machine e)`

This is the real “Gödel classical” bridge: it connects `Nat.Partrec.Code` to arithmetic syntax/semantics.

### (C4) Positive correctness (Σ₁ verification)

Goal: prove that if `e` halts, the theory proves `H e`:

- `correct : ∀ e, Rev0_K K (Machine e) → Provable_T (H e)`

This is “proof from a witness”: halting provides a finite computation certificate, which the theory can verify.

### (C5) r.e. refutability for `¬H e` (RevHalt interface requirement)

RevHalt’s Gödel-I standard interface needs r.e. **refutability**:

- `RECodePred (fun c => Provable_T (¬(H c)))`

This is usually discharged by a generic proof enumerator for `Provable_T` plus the ability to form `¬(H c)`.
RevHalt keeps it abstract to localize exactly what “effective axiomatizability” is buying you.

### (C6) Instantiate `GodelIArith` and extract the theorem

Once (C1–C5) are done, you can fill:

- `RevHalt.Arithmetic.GodelIArith` (`RevHalt/Theory/GodelIArithmetic.lean`)

and obtain automatically:
- `RevHalt.Arithmetic.GodelIArith.exists_true_unprovable`

This is the final “Gödel I standard” output: `∃ φ, Truth φ ∧ ¬ Provable_T φ`.

## 3.5.2) Concrete file/module split (recommended for a clean repo)

To keep RevHalt “interface-first” *and* make the classical instantiation manageable, a workable split is:

1. **Syntactic proof system (C1)**:
   - `RevHalt/Theory/FirstOrderProofSystem.lean`:
     proof objects + checker for first-order logic (modus ponens, generalization, equality rules).
   - `RevHalt/Theory/ArithmeticProofSystem.lean`:
     specialize to `Arithmetic.Lang` and a concrete theory (Q, PA), define `Provable_T`.
   - `RevHalt/Theory/ArithmeticProvabilityRE.lean`:
     r.e. interface for provability (`RECodePred` for “provable refutations”), plus the API lemmas you
     actually need for the Gödel lens (`Provable (¬H e)` semi-decidable).

2. **Arithmetization of computation (C3/C4)**:
   - `RevHalt/Theory/Arithmetization/Beta.lean`:
     wrappers around the β-function lemma for “sequence of witnesses” arguments.
   - `RevHalt/Theory/Arithmetization/PartrecCode.lean`:
     encode/interpret `Nat.Partrec.Code` computations as arithmetic relations.
   - `RevHalt/Theory/Arithmetization/HaltsSigma1.lean`:
     define `H : Code → Sentence` and prove `truth_H`, then prove Σ₁ correctness `halts → Provable (H e)`.

3. **Final instantiation (C6)**:
   - `RevHalt/Theory/GodelIArithmeticQ.lean`:
     assemble the Q instance of `GodelIArith` and export `exists_true_unprovable`.

This split keeps the “RevHalt machine” property: once the interfaces are filled, all “Gödel-I shape”
outputs are derived automatically by `GodelIStandard`/`GodelIArithmetic`, and the only classical strength
that remains is whatever is genuinely required by the proof checker/arithmetization layer.

## 3.6) Recommended execution order (Q-first)

The checklist (C1–C6) is accurate, but there are two big “bottlenecks”:

- (C1) building a concrete r.e. provability predicate for a theory, and
- (C3) building the computation-to-arithmetic bridge `H`.

A dependency-correct order that keeps the repo green is:

1. **Start with Robinson Q**, not PA: you already have `QTheory` and `nat_models_QTheory`.
2. **Implement `Provable_Q : Sentence → Prop`** as an r.e. predicate (proof objects + checker + enumerator),
   and package it as `RevHalt.Arithmetic.ProvabilitySystem`.
3. **Define the halting schema `H : Code → Sentence`** (Σ₁ form, typically via `Code.encodeCode` and an `evaln`/Kleene-T predicate),
   then prove `truth_H : Truth (H e) ↔ Rev0_K K (Machine e)`.
4. **Prove positive correctness**: from a concrete halting witness, build a proof of `H e` in Q
   (`Rev0_K K (Machine e) → Provable_Q (H e)`).
5. **Derive r.e. refutability**: build `RECodePred (fun c => Provable_Q (¬(H c)))` from the general proof enumerator
   plus the (computable) map `c ↦ (H c).not` (this is exactly `RevHalt.RECodePred.of_REPred_comp` once you have
   `REPred Provable_Q` and `Computable (fun c => (H c).not)`).
6. **Instantiate `GodelIArith`** and extract `exists_true_unprovable`.
7. **Optional extensions**: generalize from Q to PA (or r.e. extensions), and/or connect the RevHalt diagonal to a fully internal
   arithmetical diagonal lemma.

Notes:
- Steps (2) and (3) can be developed in parallel, but (4) strictly needs both.
- If your goal is the RevHalt “Gödel lens” (interface-first), you can stop earlier: the project already isolates exactly which
  interfaces correspond to “effective axiomatizability”, “Σ₁ verification”, and “standard-model truth”.

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
