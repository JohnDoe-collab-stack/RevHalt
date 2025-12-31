# TODO: P vs NP Formalization Roadmap

## Status: OPEN - No code yet, only conceptual framework

Goal: formalize the structural dichotomy criterion for SAT/UNSAT in a
polynomially constrained setting.

---

## Steps

### 1. Define SAT/UNSAT
- [ ] Syntax: propositional formulas (CNF or general)
- [ ] Semantics: assignments, satisfaction relation
- [ ] The ambient category of instances

### 2. Define polynomial reductions
- [ ] Morphisms: poly-time computable functions preserving SAT/UNSAT
- [ ] Show functoriality (composition, identity)
- [ ] Establish the category structure

### 3. Propose candidate operator O
- [ ] Define O on instances
- [ ] Candidate ideas:
  - Resolution closure?
  - Some form of "cumulative witness search" bounded polynomially?
  - Proof-theoretic operator?
- [ ] O must be definable uniformly, not ad-hoc

### 4. Prove universal property
- [ ] O should be adjoint/coreflector in the poly category
- [ ] Not just "some idempotent operator" - needs naturality

### 5. Prove ker_iff
- [ ] `O φ = ⊥ ↔ UNSAT φ`
- [ ] Must be a **theorem**, not a definition
- [ ] Non-tautological: kernel characterization must have content

### 6. Prove sig_invar
- [ ] `SAT (O φ) ↔ SAT φ`
- [ ] Signal preservation under the operator

### 7. Derive consequences
- [ ] If 1-6 succeed: NP/coNP is structural like Σ₁/Π₁
- [ ] The dynamics (PickWorld, omegaState) apply automatically
- [ ] P vs NP becomes: "is O poly-readable?"

### 8. Analyze criterion status
- [ ] Either: exhibit O satisfying 1-6
- [ ] Or: prove no such O exists in poly category
- [ ] Or: establish independence / barriers

---

## Key Differences from Trace/up

| Aspect | Trace/up | SAT/UNSAT |
|--------|----------|-----------|
| Space | ℕ → Prop | Formulas |
| Operator | up (cumulative) | ??? |
| Signal | Halts (∃n) | SAT (∃assignment) |
| Kernel | Stabilizes (∀n.¬) | UNSAT (∀assign.¬) |
| Constraint | None (recursive) | Polynomial |

The polynomial constraint is the hard part. `up` works because we allow
unbounded search. A poly-constrained operator must do something fundamentally
different.

---

## Potential Obstacles

1. **No natural O exists**: NP/coNP might be purely extensional at the poly level
2. **O exists but isn't poly-readable**: structure exists but P ≠ NP
3. **O exists and is poly-readable**: would imply P = NP (unlikely)
4. **Independence**: the question might not be resolvable in standard foundations

---

## Connection to Proof Complexity

The kernel `O φ = ⊥ ↔ UNSAT φ` resembles proof systems:
- A refutation system gives certificates for UNSAT
- If such certificates are poly-bounded, NP = coNP
- Cook-Reckhow framework is relevant here

Possible approach: define O via a proof system, then:
- ker_iff becomes "refutable ↔ UNSAT"
- sig_invar becomes "satisfiable ↔ has witness"
- The structural dichotomy = the proof system is complete

---

## What This Would Establish

**If O exists (satisfies 1-6)**:
- NP/coNP has the same geometric structure as Σ₁/Π₁
- The "choice" SAT/UNSAT is forced by structure (EM-regime)
- P vs NP = "can we read the structure efficiently?"

**If O doesn't exist**:
- NP/coNP is fundamentally different from Σ₁/Π₁
- Not just "harder" - geometrically different
- The dichotomy is extensional, not structural

---

## Files to Create

- [ ] `PvsNP/Syntax.lean` - formulas, CNF
- [ ] `PvsNP/Semantics.lean` - SAT, UNSAT, assignments
- [ ] `PvsNP/PolyCategory.lean` - reductions, morphisms
- [ ] `PvsNP/Operator.lean` - candidate O (if found)
- [ ] `PvsNP/StructuralDichotomy.lean` - instantiation attempt

---

## References

- Cook-Reckhow proof systems
- Propositional proof complexity
- NP vs coNP separation attempts
- Natural proofs barrier (Razborov-Rudich)
- Algebrization barrier (Aaronson-Wigderson)

---

## Honesty Note

This is speculative. The roadmap exists; the execution may hit fundamental
barriers. The value is in making the question precise:

> "Does NP/coNP admit a structural dichotomy in the sense of StructuralDichotomy?"

That question is now **formalizable**, even if not answerable.
