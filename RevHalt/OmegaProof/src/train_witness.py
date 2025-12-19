"""
train_witness.py — Training the Witness Proposer

Label logic:
- If trace Halts: Label = first index 'i' where T[i] == 1.
- If NOHALT: Label = bound (Class NULL).
"""

import argparse
import torch
import torch.nn as nn
import torch.optim as optim
from ml_bridge_t3 import generate_halting_dataset
from ml_witness import WitnessModel

def get_witness_labels(X, bound):
    # X: [batch, bound]
    # returns: [batch] (indices)
    labels = []
    for row in X:
        indices = torch.nonzero(row).view(-1)
        if indices.numel() > 0:
            labels.append(indices[0].item()) # Pick first witness
        else:
            labels.append(bound) # NULL class
    return torch.tensor(labels, dtype=torch.long)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bound", type=int, default=10)
    ap.add_argument("--epochs", type=int, default=10)
    ap.add_argument("--save", type=str, default="witness_model.pt")
    args = ap.parse_args()

    # Generate complete dataset for training (finite domain allows this)
    # Actually, let's use the generator for consistency with previous scripts
    # But for "witness", we need enough positive examples.
    
    device = torch.device("cpu")
    model = WitnessModel(args.bound).to(device)
    opt = optim.Adam(model.parameters(), lr=1e-3)
    loss_fn = nn.CrossEntropyLoss()

    print(f"Training Witness Model (Bound={args.bound})...")

    # Static dataset (all traces)
    # Reusing generation logic or just iterating all?
    # Let's generate a large batch to approximate full coverage
    # Using ml_bridge_t3 which is in the same directory (or path)
    X, y_truth, _ = generate_halting_dataset(args.bound, n_samples=5000, p_monotone=0.0) 
    # Note: p_monotone=0 (frontier focus) is good, but we need ALL halting traces ideally.
    
    y_labels = get_witness_labels(X, args.bound)

    for epoch in range(1, args.epochs + 1):
        model.train()
        opt.zero_grad()
        logits = model(X)
        loss = loss_fn(logits, y_labels)
        loss.backward()
        opt.step()
        
        # Simple/Rough Accuracy
        preds = torch.argmax(logits, dim=1)
        acc = (preds == y_labels).float().mean()
        
        print(f"Epoch {epoch}: Loss={loss.item():.4f}, Train Acc={acc:.4f}")

    torch.save(model.state_dict(), args.save)
    print(f"Saved {args.save}")

if __name__ == "__main__":
    main()
