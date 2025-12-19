# Architecture Guide: Ω-Proof KAMT System

## Overview

The **KAMT (Kernel-Aligned Multi-Task)** architecture consists of two main components:

1. **K_Ω**: Explicit proof kernel (Oracle)
2. **A_θ**: Neural attention encoder (Learner)

---

## 1. Proof Kernel (K_Ω)

### Purpose
Provides ground-truth labels `(y*, halt_rank)` by explicitly running a proof search with early stopping.

### Implementation: `ProofKernel`

```python
class ProofKernel:
    def compute_t_first_taut(self, formula, valuation_order="lex", atom_order="sorted"):
        """
        Stop on first counterexample.
        
        Returns:
            (verdict: bool, t_first: int)
        """
```

### Key Parameters

- **`valuation_order`**: Order Ω for exploring truth assignments
  - `"lex"`: Lexicographic (deterministic, baseline)
  - `"shuffle"`: Random permutation (destroys geometry)
  - `"random"`: Monte Carlo sampling
  
- **`atom_order`**: Order σ for variable naming
  - `"sorted"`: p0, p1, p2, ... (canonical)
  - `"shuffle"`: Random permutation (tests atom-invariance)

### Output Labels

1. **`y*`**: Ground truth (TAUT=1 or SAT=1)
2. **`t_first`**: Steps to first witness/counterexample
3. **`halt_rank`**: Discretized difficulty
   - `EARLY` (0): `t_first / 2^n ≤ 0.25`
   - `MID` (1): `0.25 < t_first / 2^n ≤ 0.75`
   - `LATE` (2): `t_first / 2^n > 0.75`

---

## 2. Neural Encoder (A_θ)

### Purpose
Learn to predict `(y*, halt_rank)` from formula structure alone.

### Architecture: `ProofModel`

```
Input: Formula φ (prefix notation)
  │
  ├─→ Token Embedding (vocab_size → embed_dim)
  ├─→ Position Embedding (MAX_LEN → embed_dim)
  │
  └─→ [Combined] (batch, seq_len, embed_dim)
       │
       ├─→ Multi-Head Attention (4 heads)
       │
       └─→ AdaptiveAvgPool → (batch, embed_dim)
            │
            ├─→ Concatenate with Question Type Embedding
            │
            └─→ MLP (embed_dim*2 → hidden_dim → ... → hidden_dim)
                 │
                 ├─→ Y-head (hidden_dim → 1) [Binary]
                 └─→ Halt-head (hidden_dim → 3) [Multiclass]
```

### Components

1. **Token Embedding**
   - **Vocabulary**: `{PAD, p0, p1, ..., NOT, AND, OR, IMPLIES}`
   - **Encoding**: Prefix notation (e.g., `IMPLIES AND p0 p1 NOT p0` for `(p0 ∧ p1) → ¬p0`)

2. **Multi-Head Attention**
   - **Heads**: 4
   - **Purpose**: Capture long-range dependencies in formula structure

3. **Question Type Embedding**
   - `TAUT` vs `SAT` (different semantics)

4. **MLP Backbone**
   - **Depth**: 3 layers (configurable)
   - **Activation**: ReLU

5. **Dual Heads**
   - **Y-head**: Binary classification (BCE loss)
   - **Halt-head**: 3-class classification (CE loss)

---

## 3. Multi-Task Objective

### Loss Function

```python
loss = loss_Y + λ · loss_Halt
```

- **`loss_Y`**: `BCE(y*, ŷ)` — Semantic correctness
- **`loss_Halt`**: `CE(halt_rank, halt_hat)` — Computational difficulty
- **`λ`**: Balance parameter (default: 0.5)

### Training Loop

```python
for epoch in range(epochs):
    for formula, q_type, depth, y, halt in train_loader:
        y_logits, halt_logits, _ = model(formula, q_type, depth)
        
        loss_y = BCE(y_logits, y)
        loss_h = CE(halt_logits, halt)
        
        loss = loss_y + λ * loss_h
        loss.backward()
        optimizer.step()
```

---

## 4. Data Flow

```
┌─────────────────┐
│ Random Formula  │ n_atoms=3, depth=2
│   (p0 ∨ ¬p1)    │
└────────┬────────┘
         │
         ├─→ ProofKernel.compute_t_first_taut(formula, order="lex")
         │    └─→ (y*=1, t_first=2)
         │         └─→ halt_rank=EARLY (2/2^3 = 0.25)
         │
         └─→ encode_formula(formula)
              └─→ [OR, ATOM_1, NOT, ATOM_2, PAD, PAD, ...]
                   │
                   └─→ ProofModel(encoded, q_type=SAT)
                        └─→ (ŷ, halt_hat)
```

---

## 5. Ablation: Shuffle-K

### Purpose
Test if model learns **structure** or just **statistics**.

### Implementation

```python
if shuffle_K:
    # Randomize halt_rank labels
    halt_ranks = [s.halt_rank for s in samples]
    random.shuffle(halt_ranks)
    # Reassign to samples
```

### Expected Behavior

- **K-real**: High halt accuracy (~96% val, ~75% OOD)
- **Shuffle-K**: Low halt accuracy (~37% val, ~33% OOD)

**Interpretation**: The ~59pp drop proves the model was learning the **oracle structure**, not just formula complexity.

---

## 6. Evaluation Metrics

### A. Accuracy

- **Y-head**: Binary accuracy (TAUT/SAT)
- **Halt-head**: 3-class accuracy (EARLY/MID/LATE)

### B. Balanced Accuracy (Stress Test)

```python
from sklearn.metrics import balanced_accuracy_score

bal_acc = balanced_accuracy_score(y_true, y_pred)
```

**Why**: Handles class imbalance (EARLY formulas may dominate).

### C. Per-Class Recall

```python
from sklearn.metrics import confusion_matrix

cm = confusion_matrix(y_true, y_pred, labels=[0, 1, 2])
recalls = [cm[i, i] / cm[i, :].sum() for i in range(3)]
```

**Interpretation**: 
- High EARLY recall + Low MID/LATE recall → Model can't predict deep halts

---

## 7. Hyperparameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `embed_dim` | 32 | Token/position embedding size |
| `hidden_dim` | 128 | MLP hidden layer size |
| `n_layers` | 3 | MLP depth |
| `n_heads` | 4 | Attention heads |
| `λ` | 0.5 | Multi-task loss weight |
| `lr` | 1e-3 | Learning rate |
| `batch_size` | 64 | Batch size |

### Tuning Recommendations

- **Increase `hidden_dim`**: If underfitting (low train accuracy)
- **Decrease `λ`**: If Y-head converges but Halt-head doesn't
- **Increase `n_layers`**: For deeper formulas (test OOD = depth 5)

---

## 8. Model Capacity

**Total Parameters**: ~50K-100K (depending on config)

```
Embedding: vocab_size × embed_dim = 20 × 32 = 640
Attention: ~4 × embed_dim^2 = 4 × 32^2 = 4,096
MLP: ~3 × hidden_dim^2 = 3 × 128^2 = 49,152
Heads: hidden_dim × (1 + 3) = 128 × 4 = 512
──────────────────────────────────────────────
Total: ~54K parameters
```

**Design Choice**: Deliberately **shallow** to test structural learning (not brute-force memorization).

---

## References

- **Implementation**: `src/proof_kernel.py`, `src/train.py`
- **Configuration**: `configs/default_config.yaml`
- **Lean Analogy**: `docs/LINK_TO_LEAN.md`
