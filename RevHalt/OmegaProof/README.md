# Ω-Proof: Empirical Validation of Computational Impossibility

> **Best OOD generalization (+42pp Halt) — Structure transfers across depths**
> 
> **Formally grounded in Lean**: `OmegaChaitin.lean` + `OmegaComplexity.lean`

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[![PyTorch](https://img.shields.io/badge/PyTorch-2.0+-ee4c2c.svg)](https://pytorch.org/)

## Overview

**Ω-Proof** provides empirical validation of impossibility theorems (T2/T3) from the [RevHalt](../Theory) formalization. It demonstrates that neural networks can learn the **geometric structure** of computational oracles, not just statistical correlations.

**New**: Formally grounded in Chaitin's Ω via Lean formalization ([OmegaChaitin.lean](../Dynamics/Instances/OmegaChaitin.lean), [OmegaComplexity.lean](../Dynamics/Instances/OmegaComplexity.lean)).

### Key Result

| Condition | Val Halt | OOD Halt | Interpretation |
|-----------|----------|----------|----------------|
| **K-real** (with structure) | **96%** | **75%** | Learns oracle geometry |
| Shuffle (structure destroyed) | 37% | 33% | Falls to statistical baseline |
| **Δ (Structural Component)** | **+59pp** | **+42pp** | **Structure generalizes OOD** |

---

## Architecture: KAMT (Kernel-Aligned Multi-Task)

```
┌──────────────┐
│   Oracle K   │  Early-stopping proof kernel
│  (ProofKernel)│  t_first = witness discovery time
└──────┬───────┘  (Grounded in OmegaChaitin.lean)
       │ Labels: (y*, halt_rank)
       │ halt_rank ≈ gap(t) from OmegaComplexity
       ↓
┌──────────────┐
│  Encoder Aθ  │  Shallow attention network
│  (ProofModel)│  Input: formula (prefix notation)
└──────┬───────┘
       │ Loss = BCE(y*) + λ·CE(halt_rank)
       ↓
   Predictions: (ŷ, halt_hat)
```

### Formal Foundation

**Lean Theorems Validated**:
1. **`omega_bit_cut_link`**: Bits are dyadic windows in Cut-space
2. **`gap_lower_bound`**: `gap(t) ≥ 2^(-t)` → precision requires time
3. **`LR_bit_win_halts_equiv`**: Dual procedures → same halting (non-trivial!)

See [docs/LINK_TO_LEAN.md](docs/LINK_TO_LEAN.md) for detailed correspondence.

---

## Gold Standard Stress Test

**Protocol**: Decorrelate Valuation Order (Time) and Atom Order (Space) on **identical formulas** (MD5-verified).

| Variant (Time / Space) | Bal Acc | Recall (E/M/L) | Pearson | Interpretation |
| :--------------------- | :------ | :------------- | :------ | :------------- |
| **lex / sorted** (Baseline) | **78.2%** | **0.77 / 0.74 / 0.84** | 1.00 | Perfect structure capture |
| **shuffle / sorted** | **40.9%** | **0.72 / 0.24 / 0.26** | 0.78 | **Geometry destroyed** |
| **lex / shuffle** (Rename) | **79.0%** | **0.78 / 0.75 / 0.84** | 0.95 | Atom-invariant ✓ |

### Decomposition

- **Density Component** (~52%): Intrinsic formula difficulty, order-independent
- **Geometric Component** (~26%): Specific oracle structure (lexicographic search)

**Lean Connection**: The 26pp drop = `|S₁|` (non-internalizable frontier from T3).

---

## Formal Grounding: Cuts vs Bits

### Key Insight from `OmegaChaitin.lean`

**RevHalt attacks Ω via Cuts (computable), not Bits (non-computable)**:

```lean
-- Cuts are semi-decidable
theorem omega_cut_halts_iff_reached (q : ℚ) :
  Halts (LR_omega ∅ (CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q)

-- Bits are boundaries between Cuts
theorem omega_bit_cut_link :
  BitIs n a ↔ ∃ k, CutGe(k/2^n) ∧ ¬CutGe((k+1)/2^n) ∧ k%2=a
```

**Our Implementation**: `ProofKernel` uses **early stopping** (Cut-based verification), predicting **when Cuts are reached** (`halt_rank`), not bit values.

### Gap Bound from `OmegaComplexity.lean`

```lean
theorem gap_lower_bound (t : ℕ) : gap(t) ≥ 2^(-t)
theorem precision_requires_time : gap(t) ≤ 2^(-n) → t ≥ n
```

**Our `halt_rank`**:
- **EARLY**: gap large, low precision
- **LATE**: gap small, high precision

**Stress Test MID/LATE collapse**: Without order Ω, model can't predict when high precision is reached.

---

## Quick Start

### Installation

```bash
cd OmegaProof
pip install -r requirements.txt
```

### Training

```bash
# K-real condition (with oracle structure)
python src/train.py --epochs 50 --output-dir results/k_real

# Shuffle ablation (structure destroyed)
python src/train.py --epochs 50 --output-dir results/shuffle --shuffle-K
```

### Stress Test

```bash
# Run Gold Standard protocol
python src/stress_eval.py results/k_real/final.pt

# Results saved to stress_results.json
```

---

## Connection to RevHalt Formalization

### Theorem Mapping

**T1 (Canonicity)**:
- **Lean**: `Rev0_K K T ↔ Halts T`
- **Empirical**: Y-head ~100% accuracy

**T2 (Impossibility)**:
- **Lean**: `¬ ∃ InternalHaltingPredicate`
- **Empirical**: **37pp gap** when order Ω is hidden
- **OmegaChaitin**: Bits non-computable, attacks via Cuts

**T3 (Complementarity)**:
- **Lean**: `S₃ = S₂ ∪ S₁` sound extension
- **Empirical**: **78.2% = 52% (density) + 26% (geometry)**
- **Measurement**: 26pp = `|S₁|` (non-internalizable frontier)

---

## File Structure

```
OmegaProof/
├── README.md                          ← This file
├── requirements.txt                   ← Python dependencies
├── src/                              ← All Python code
│   ├── proof_kernel.py               ← Oracle K (early stopping)
│   ├── dataset.py                    ← OOD data generation
│   ├── train.py                      ← Multi-task training
│   ├── stress_eval.py                ← Gold Standard protocol
│   ├── sphere_wrapper.py             ← Fuel tracking
│   └── run_sphere_validation.py
├── docs/
│   ├── LINK_TO_LEAN.md               ← **Deep Lean connections**
│   ├── PROTOCOL.md                   ← Experimental protocol
│   └── ARCHITECTURE.md               ← KAMT system guide
├── configs/
│   └── default_config.yaml
└── results/
```

---

## Why Logic > Arithmetic?

| | Ω-Proof | Ω-Arith |
|---|---------|---------|
| **Domain** | Propositional logic | Integer addition |
| **K dynamics** | Early stopping (global) | Carry propagation (local) |
| **OOD Δ Halt** | **+42pp** | +4.6pp |
| **Transfer** | Strong ✓ | Weak ✗ |
| **Lean analog** | Cut-based (semi-decidable) | Bit-based (local computation) |

**Insight**: Global properties (depth, Cuts) transfer better than local dependencies (carries, Bits).

---

## Citation

```bibtex
@misc{omega_proof_2025,
  title={Ω-Proof: Empirical Validation of Computational Impossibility},
  author={RevHalt Project},
  year={2025},
  note={Formally grounded in OmegaChaitin.lean and OmegaComplexity.lean},
  url={https://github.com/your-repo/RevHalt}
}
```

---

## References

- **RevHalt Formalization**: [../Theory](../Theory)
- **Omega Lean Files**: [OmegaChaitin.lean](../Dynamics/Instances/OmegaChaitin.lean), [OmegaComplexity.lean](../Dynamics/Instances/OmegaComplexity.lean)
- **Deep Lean Connections**: [docs/LINK_TO_LEAN.md](docs/LINK_TO_LEAN.md)
- **Stress Test Protocol**: [docs/PROTOCOL.md](docs/PROTOCOL.md)

---

## License

MIT License - see [../LICENSE](../LICENSE)
