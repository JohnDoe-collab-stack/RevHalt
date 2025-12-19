# Ω-Proof Quickstart

Follow these steps to replicate the **T3 Architecture Results**.

## 1. Verify the Architecture
Run the "Anti-Cheat" and "Hardening" suites to confirm S1/S2 separation and soundness.
```bash
cd src
python test_anti_cheat.py
python test_hardening.py
```
*Expected: "PASS"*

## 2. Train the Witness Proposer
Train the ML model to find witnesses for S2.
```bash
python train_witness.py --bound 10 --epochs 10
```

## 3. Measure Internalization Gain
See how much the ML helps S2 without compromising soundness.
```bash
python eval_heuristic.py
```
*Expected: S2 Coverage jumps from ~1% to >70%.*

## 4. See a Proof Certificate
Run the demo to see a specific non-monotone trace being decided with a certificate.
```bash
python demo_proof_object.py
```
*Expected output includes `Cert: {'logic': 'Witness', 'index': ...}`*
