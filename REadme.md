# RevHalt

A Lean 4 framework proving that computational truth (halting) is:
- **Canonical** — independent of how you observe it
- **Inaccessible** — no sound formal system fully captures it
- **Complementary** — any sound theory can be strictly extended toward it

Unlike classical presentations of Gödel's theorems, which work *inside* a specific theory, RevHalt provides the abstract framework and treats theories (PA, ZFC) as instances to be plugged in.

---

## Quick Start

```lean
import RevHalt.Main
open RevHalt

-- Access all core definitions and theorems
#check T1_traces
#check T2_impossibility
#check T3_strong
#check RevHalt_Master_Complete
```

```bash
lake build
```

---

## Architecture

The project follows a **Layered Modular Architecture**:

```
RevHalt/
├── Base/                # Foundation layer
│   ├── Trace.lean       # Trace, Halts, up operator
│   └── Kit.lean         # RHKit, DetectsMonotone, Rev_K
│
├── Theory/              # Abstract theorems (theory-independent)
│   ├── Canonicity.lean  # T1_traces, DynamicBridge, verdict_K
│   ├── Impossibility.lean # T2_impossibility, TuringGodelContext'
│   └── Complementarity.lean # T3_strong, InfiniteIndependentHalting
│
├── Kinetic/             # Dynamic semantics
│   ├── Closure.lean     # CloK, CloRev, Stage
│   ├── MasterClosure.lean # VerifiableContext, TheGreatChain
│   └── System.lean      # Gap, GapTruth, GapSystem
│
├── Oracle.lean          # Framework as Truth Oracle
│
├── Bridge/              # M/L/A/E instantiation layer
│   ├── RigorousModel.lean # RigorousModel, SoundLogicDef, Arithmetization
│   ├── Context.lean     # EnrichedContext, ProvableSet
│   ├── Master.lean      # RevHalt_Master_Complete
│   └── Coded/           # Coded formula families (for PA/ZFC)
│       ├── Interface.lean
│       ├── Context.lean
│       └── Master.lean
│
├── Extensions/          # Advanced applications
│   ├── RefSystem.lean   # Cut/Bit dynamic verification
│   └── OmegaChaitin.lean # Chaitin's Ω as RefSystem
│
├── Instances/           # Concrete theory instances
│   ├── Arithmetization.lean # PRModel (Mathlib Partrec)
│   └── PA/              # Peano Arithmetic instance
│
└── Main.lean            # Public API entry point
```

### Layer Dependencies

```
Base → Theory → Kinetic → Oracle
  ↓       ↓                  ↓
  └───────┴──────→ Bridge ←──┘
                      ↓
              Extensions / Instances
```

---

## The Three Theorems

### T1 — Canonicity

**Claim**: Computational truth is objective — independent of observation mechanism.

```lean
theorem T1_traces (K : RHKit) (hK : DetectsMonotone K) :
    ∀ T, Rev0_K K T ↔ Halts T
```

- Any valid Kit yields the same verdict as standard halting
- `T1_uniqueness`: Two valid Kits are extensionally equivalent
- `T1_semantics`: Under DynamicBridge, Rev captures model-theoretic consequence

### T2 — Impossibility (Turing-Gödel Synthesis)

**Claim**: No internal predicate can be Total, Correct, and Complete.

```lean
theorem T2_impossibility {Code PropT : Type} (ctx : TuringGodelContext' Code PropT) :
    ¬∃ H : InternalHaltingPredicate ctx, H.total ∧ H.correct ∧ H.complete
```

This extracts the common abstract core of Turing's undecidability and Gödel's incompleteness via the `diagonal_program` axiom.

### T3 — Complementarity

**Claim**: Rev is the complement of any sound formal system.

```lean
theorem T3_strong {Code PropT : Type} (ctx : TuringGodelContext' Code PropT)
    (iih : InfiniteIndependentHalting Code PropT ctx) :
    ∃ (Index : Type) (π : Partition Index),
      π.infinite ∧ π.disjoint ∧ (∀ i, extends_proven (π.family i))
```

Under the `InfiniteIndependentHalting` hypothesis, there exist **infinitely many disjoint, compatible directions** of extension. Truth and provability are not opposed — they are **complementary**.

---

## The Oracle Perspective

The framework acts as a **Truth Oracle** external to any internal theory.

```lean
structure TruthOracle (PropT : Type) where
  judge : PropT → Prop
  sound : ∀ p, judge p → Truth p

theorem oracle_not_internalizable (ctx : VerifiableContext PropT) :
    ¬∃ (internal : PropT → Prop), (∀ p, internal p ↔ oracle.judge p)
```

The bridge (`Truth ↔ Halts LR`) provides verdicts inaccessible to the theory's internal logic.

---

## M/L/A/E Interface

The framework factors assumptions into four pluggable components:

| Component | Type | Purpose |
|-----------|------|---------|
| **M** | `RigorousModel` | Computability model (Code, Program, diagonal_halting) |
| **L** | `SoundLogicDef PropT` | Logic (Provable, Truth, soundness) |
| **A** | `Arithmetization M PropT L` | Maps definability to provability |
| **E** | `HaltEncode + encode_correct` | Maps halting to semantic truth |

### Master Theorem

```lean
theorem RevHalt_Master_Complete (M : RigorousModel) (K : RHKit)
    (hK : DetectsMonotone K) (L : SoundLogicEncoded M PropT) :
    let ctx := EnrichedContext_from_Encoded M K hK L
    -- T1: Canonicity
    (∀ e, ctx.RealHalts e ↔ Halts (rmCompile M e)) ∧
    -- T2: True but unprovable exists
    (∃ p, ctx.Truth p ∧ ¬ctx.Provable p) ∧
    -- T2': Independent code exists
    (∃ e, ¬ctx.Provable (ctx.H e) ∧ ¬ctx.Provable (ctx.Not (ctx.H e))) ∧
    -- T3: Strict sound extension exists
    (∃ T1 : Set PropT, ProvableSet ctx ⊂ T1 ∧ (∀ p ∈ T1, ctx.Truth p))
```

---

## Kinetic Layer

The dynamic semantics formalize the evolution of truth over time:

| Concept | Definition |
|---------|------------|
| `CloK Γ` | Kinetic closure: sentences eventually true |
| `CloRev K Γ` | Rev-based closure via halting |
| `Gap` | Difference between kinetic truth and provability |
| `GapSystem` | Kit-invariant gap reasoning |
| `TheGreatChain` | Truth = CloK = Halts = Rev verdict |

---

## Instances

### PRModel (Mathlib)

Complete instance using `Nat.Partrec.Code`:

```lean
-- RevHalt/Instances/Arithmetization.lean
def PRModel : RigorousModel  -- No sorry, no axioms
theorem PRModel_Master_Theorem : ... -- Full T1+T2+T2'+T3
```

### Peano Arithmetic

Coded instance for PA:

```lean
-- RevHalt/Instances/PA/Main.lean
theorem PA_Master_Theorem : ... -- T1 + Diagonal for coded families
```

---

## Extensions

### RefSystem

Cut/Bit framework for dynamic verification:

```lean
structure RefSystem (Model Sentence Referent : Type) where
  Sat : Model → Sentence → Prop
  Cut : ℚ → Referent → Sentence
  Bit : ℕ → ℕ → Referent → Sentence
  cut_mono : ...
  bit_cut_link : ...
```

### OmegaChaitin

Chaitin's Ω as a RefSystem instance, enabling Rev-based reasoning about algorithmic randomness.

---

## Build & Validate

```bash
# Build everything
lake build

# Validate demos
lake env lean RevHalt/Demo/All.lean

# Check specific modules
lake build RevHalt.Main
lake build RevHalt.Instances.PA.Main
```

---

## Design Principles

1. **Compositionality**: Once a theory provides M/L/A/E, all theorems transport automatically
2. **No implicit decidability**: `PredDef` is `Prop`-valued (definability, not decidability)
3. **Explicit soundness**: `Provable → Truth` is a hypothesis, not ambient
4. **Modular layers**: Each layer has clear responsibilities and dependencies

---

## LLM Disclosure

The code and documentation in this repository were primarily generated by Large Language Models under strict conceptual guidance from the author.

**Methodology:**
- **Conceptual Design**: Core definitions and theorem statements specified by the author
- **Implementation**: Expansion into Lean 4 code via iterative generation and refinement
- **Verification**: The Lean 4 kernel is the final authority

This project demonstrates how agentic AI can translate private conceptual frameworks into rigorous, machine-checked mathematical artifacts.
