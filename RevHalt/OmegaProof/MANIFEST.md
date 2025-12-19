# OmegaProof - Project Manifest

**Last updated**: 2025-12-19

## 🎯 Quick Start (3 steps)

```bash
# 1. Train model
python src/train.py --epochs 100

# 2. Run Gold Standard evaluation
python src/stress_eval.py outputs/gold_standard_baseline/final.pt

# 3. Check results
cat outputs/gold_standard_baseline/stress_results.json
```

---

## 📁 Project Structure

```
OmegaProof/
├── README.md              # Project overview
├── MANIFEST.md           # This file (file guide)
├── FILE_STRUCTURE.md     # Detailed structure
├── requirements.txt      # Dependencies
│
├── src/                  # Source code
│   ├── proof_kernel.py   # ⭐ Oracle Ω implementation
│   ├── dataset.py        # ⭐ Data generation
│   ├── train.py          # ⭐ Training loop
│   ├── stress_eval.py    # ⭐ Gold Standard evaluation
│   ├── sphere_wrapper.py # Sphere integration (optional)
│   ├── run_sphere_validation.py
│   └── tests/            # Validation tests
│
├── docs/                 # Documentation
│   ├── PROTOCOL.md       # Gold Standard protocol
│   ├── LINK_TO_LEAN.md   # Lean formalization links
│   └── ARCHITECTURE.md   # System architecture
│
├── configs/              # Configurations
│   └── default_config.yaml
│
├── outputs/              # Training outputs (gitignored)
└── results/              # Evaluation results (gitignored)
```

---

## ⭐ ESSENTIAL FILES (Core - 4 files)

### 1. `src/proof_kernel.py`
**Purpose**: Ω-oracle implementation  
**Key components**:
- `Formula` classes (Atom, Not, And, Or, Implies)
- `ProofKernel`: Oracle with early stopping
- `compute_t_first_taut/sat`: Decision procedures
- `halt_rank_of_tfirst`: EARLY/MID/LATE classification

### 2. `src/dataset.py`
**Purpose**: Generate training/validation/test data  
**Key components**:
- `ProofSample`: Data structure
- `generate_samples`: Sample generation with RNG isolation
- `generate_dataset`: Train/Val/Test split (Gold Standard config)
- `encode_formula`: Token encoding

**Current config**:
- Train/Val: depth 1-3, atoms 2-3
- Test OOD: depth 5-8, atoms 3-4 (strict depth ≥ 5)

### 3. `src/train.py`
**Purpose**: Multi-task training (Y* + halt_rank)  
**Key components**:
- `ProofModel`: Transformer encoder
- `train()`: Training loop with balanced accuracy
- PAD masking, CUDA auto-detect, gap metrics

### 4. `src/stress_eval.py`
**Purpose**: **Gold Standard evaluation** (THE KEY TEST)  
**Variants tested**:
- Baseline (lex/sorted)
- Shuffle time (shuffle/sorted) ← Tests oracle structure
- Shuffle space (lex/shuffle) ← Tests atom invariance

**Expected**: 26pp gap between baseline and shuffle-time

---

## 📚 DOCUMENTATION (4 files)

### `README.md`
High-level overview, key results, quick start

### `docs/PROTOCOL.md`
Gold Standard stress test methodology

### `docs/LINK_TO_LEAN.md`
Formal correspondence to RevHalt theorems (T1/T2/T3)

### `docs/ARCHITECTURE.md`
KAMT architecture (Kernel-Aligned Multi-Task)

---

## 🧪 TESTS (Optional - for validation only)

### Core Validation
- `tests/test_audit_fixes.py`: Audit fixes validation
- `tests/test_gold_standard.py`: Correctness verification
- `tests/test_standard.py`: Standard test suite

### Limit Testing (informational)
- `tests/test_high_complexity.py`
- `tests/test_extreme_limits.py`
- `tests/test_ultra_deep.py`

### Lean Validation
- `tests/test_lean_validation.py`: Lean-grounded properties

**Note**: All tests are for development/validation. Not needed for training/eval.

---

## 🔧 CONFIGURATION

### `configs/default_config.yaml`
Default training parameters (currently unused, CLI args used instead)

### `requirements.txt`
Python dependencies:
- PyTorch
- NumPy, Pandas
- scikit-learn
- lxml (Sphere integration)

---

## 📊 OUTPUTS (Generated, gitignored)

### `outputs/`
Training checkpoints and logs
- `outputs/gold_standard_baseline/final.pt` ← Final model

### `results/`
Evaluation results
- Stress test JSON files
- Gap analysis

---

## 🗑️ OBSOLETE/CLEANUP CANDIDATES

**Can be deleted** (if not in use):
- `outputs/quick_test/`
- `outputs/final_corrected/`
- `outputs/final_v2/`
- `outputs/test_logs/`

**Keep only**:
- `outputs/gold_standard_baseline/` ← Current training

---

## 🚀 WORKFLOW

### Training
```bash
python src/train.py --epochs 100 --output-dir outputs/my_run
```

### Evaluation
```bash
python src/stress_eval.py outputs/my_run/final.pt
```

### Tests (optional)
```bash
python src/tests/test_audit_fixes.py
python src/tests/test_standard.py
```

---

## 📝 KEY METRICS

**Expected Results** (Gold Standard):
- Baseline (lex/sorted): **~78% balanced accuracy**
- Shuffle time: **~41%** (26pp drop)
- Shuffle space: **~79%** (stable)

**Current Training** (Epoch 10):
- Val Y: 97.2%
- Val H: 87.8% (bal: 87.3%)
- On track for good results ✅

---

## 🎯 NEXT STEPS

1. **Wait for training to complete** (~1-2h)
2. **Run stress_eval** (10min)
3. **Verify 26pp gap**
4. **Publication ready** ✅
