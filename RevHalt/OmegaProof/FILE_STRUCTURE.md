# OmegaProof - File Structure

## Directory Layout

```
OmegaProof/
├── README.md           # Main documentation
├── requirements.txt    # Python dependencies
├── configs/            # Configuration files
│   └── default_config.yaml
├── docs/               # Documentation
│   ├── PROTOCOL.md     # Gold Standard protocol
│   ├── LINK_TO_LEAN.md # Lean formalization links
│   └── ARCHITECTURE.md # System architecture
├── src/                # Source code
│   ├── proof_kernel.py       # Oracle kernel
│   ├── dataset.py            # Dataset generation
│   ├── train.py              # Training loop
│   ├── stress_eval.py        # Stress evaluation
│   ├── sphere_wrapper.py     # Sphere integration
│   ├── run_sphere_validation.py
│   └── tests/                # Test suite (26+ tests)
│       ├── README.md
│       ├── test_audit_fixes.py
│       ├── test_gold_standard.py
│       ├── test_standard.py
│       └── ...
├── outputs/            # Training outputs
│   └── quick_test/    # Quick test checkpoints
└── results/            # Evaluation results
```

## Core Files

- **proof_kernel.py**: Ω-oracle with early stopping
- **dataset.py**: Ultra-deep formula generation (depth 15-30)
- **train.py**: Multi-task training (Y* + halt_rank)
- **stress_eval.py**: Gold Standard evaluation

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Run standard tests
python src/tests/test_standard.py

# Train model (ultra-deep)
python src/train.py --epochs 10

# Run stress evaluation
python src/stress_eval.py outputs/final.pt
```

## Configuration

**Current Standard**: Ultra-deep formulas (depth 15-30)
- Train: depth 15-25, atoms 5-6
- Val: depth 15-25, atoms 5-6
- Test OOD: depth 25-30, atoms 6-7

See `src/dataset.py::generate_dataset()` for details.
