# Ω-Proof File Structure

```
OmegaProof/
├── README.md               # Project Overview (T3 Architecture)
├── MANIFEST.md             # Component Descriptions
├── FILE_STRUCTURE.md       # Directory Layout (This file)
├── QUICKSTART.md           # How to Run
├── src/
│   ├── proof_kernel.py     # Core Logic (The Physics)
│   ├── t3_types.py         # Verdict Definitions
│   │
│   ├── s1_oracle.py        # S1: External Truth
│   ├── s2_extended.py      # S2: Internal Logic
│   ├── t3_policy.py        # S3: Total System
│   │
│   ├── ml_witness.py       # ML: Witness Neural Net
│   ├── s2_heuristic.py     # ML-Guided Verification
│   ├── train_witness.py    # Training Script
│   ├── eval_heuristic.py   # Metrics Script
│   │
│   ├── demo_proof_object.py # Execution Proof Demo
│   ├── test_hardening.py   # Strict Bounds Checks
│   ├── test_anti_cheat.py  # Architectural Integrity
│   └── test_t3_corrected.py # Unit Tests
│
└── witness_model.pt        # Trained Model
```
