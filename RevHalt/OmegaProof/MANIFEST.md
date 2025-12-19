# Ω-Proof Manifest

## Source Code (`src/`)

### Core (Kernel & Types)
*   `proof_kernel.py`: The executable implementation of `RevHalt.Base`. Defines `FiniteTrace`, `Halts`, `Verdicts`.
*   `t3_types.py`: Definitions for `Decision` and `Verdict` (HALTS, NOHALT, UNKNOWN).

### Components (T3 Agents)
*   `s1_oracle.py`: **S1 (The Oracle)**. Wraps `Rev0_K` to provide absolute truth.
*   `s2_extended.py`: **S2 (The Prover)**. Implements Monotone logic and Witness verification.
*   `t3_policy.py`: **S3 (The Policy)**. Routes decisions (S2 -> S1) to ensure totality.
*   `ml_witness.py`: **ML (The Guide)**. Neural network proposing witness indices.
*   `s2_heuristic.py`: **Heuristic Policy**. Combines S2 and ML in a Propose-Verify loop.

### Validation & Training
*   `test_hardening.py`: **Strict Verification**. Ensures strict bounds, provenance, and oracle independence.
*   `test_anti_cheat.py`: **Anti-Cheat Suite**. Verifies structural separation of S1/S2.
*   `demo_proof_object.py`: **Proof Demo**. Generates a concrete proof certificate for a non-monotone trace.
*   `train_witness.py`: Training script for the Witness Proposer.
*   `eval_heuristic.py`: Evaluation script measuring S2 Internalization Gain.

## Key Artifacts
*   `witness_model.pt`: Trained weights for the Witness Proposer (Bound=10).
