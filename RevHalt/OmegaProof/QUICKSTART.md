# Quick Start Guide

## Installation

```bash
pip install -r requirements.txt
```

## Run Experiment (3 commands)

### 1. Train Model (2-3 hours)
```bash
python src/train.py --epochs 100
```

### 2. Evaluate Gold Standard (10 minutes)
```bash
python src/stress_eval.py outputs/gold_standard_baseline/final.pt
```

### 3. Check Results
```bash
# Results saved in outputs/gold_standard_baseline/stress_results.json
# Expected:
# - Baseline (lex/sorted): ~78% acc
# - Shuffle time: ~41% acc (26pp drop)
# - Shuffle space: ~79% acc
```

## Understanding the Results

**The 26pp Gap** proves:
- ✅ Model learned oracle structure (T2)
- ✅ But cannot fully internalize it (T3)
- ✅ Empirical validation of impossibility theorems

## Files You Need to Know

- **`src/proof_kernel.py`**: Oracle Ω
- **`src/dataset.py`**: Data generation
- **`src/train.py`**: Training
- **`src/stress_eval.py`**: Gold Standard test
- **`docs/PROTOCOL.md`**: Full methodology

Everything else is optional/tests.

## Questions?

See `MANIFEST.md` for complete file guide.
