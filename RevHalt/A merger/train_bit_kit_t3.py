"""
train_bit_kit_t3.py — T3-aligned training for the BitKit model (S1 only)

Key idea:
- S2 decides monotone traces exactly (proof-like).
- S1 (ML) is trained primarily on the *frontier*: non-monotone traces.
- No "null margin" hack: null trace is monotone and is handled by S2.

This typically reduces the weird low-Hamming-weight FN cluster that appeared when
we forced S1 to be canonical on monotone traces.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import math
import os

import torch
import torch.nn as nn
import torch.optim as optim

from ml_bridge_t3 import generate_halting_dataset
from s1_kit import S1Kit
from t3_policy import T3HaltingPolicy
from eval_t3 import exact_metrics_policy, monotone_failure_cases


class BitKitMLP(nn.Module):
    def __init__(self, bound: int, hidden: int = 64):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(bound, hidden),
            nn.ReLU(),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
            nn.Linear(hidden, 1),
        )

    def forward(self, x):
        return self.net(x)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bound", type=int, default=10)
    ap.add_argument("--epochs", type=int, default=5)
    ap.add_argument("--batch_size", type=int, default=512)
    ap.add_argument("--device", type=str, default="cpu")
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--p_monotone", type=float, default=0.5)
    ap.add_argument("--pos_weight", type=float, default=1.0)
    ap.add_argument("--eps", type=float, default=0.10, help="selective decision epsilon (policy)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--save", type=str, default="bitkit_t3.pt")
    args = ap.parse_args()

    torch.manual_seed(args.seed)

    device = torch.device(args.device)
    model = BitKitMLP(args.bound).to(device)

    pos_weight = torch.tensor([args.pos_weight], dtype=torch.float32, device=device)
    loss_fn = nn.BCEWithLogitsLoss(pos_weight=pos_weight)
    opt = optim.Adam(model.parameters(), lr=args.lr)

    for epoch in range(1, args.epochs + 1):
        model.train()

        X, y, is_m = generate_halting_dataset(args.bound, args.batch_size, p_monotone=args.p_monotone, seed=args.seed + epoch)
        X = X.to(device)
        y = y.to(device)
        is_m = is_m.to(device)

        # Train on frontier: non-monotone only
        nm = ~is_m
        if nm.sum().item() == 0:
            # degenerate (unlikely) — fall back to full batch
            X_nm, y_nm = X, y
        else:
            X_nm, y_nm = X[nm], y[nm]

        opt.zero_grad(set_to_none=True)
        logits = model(X_nm)
        loss = loss_fn(logits, y_nm)
        loss.backward()
        opt.step()

        # Evaluation (exact) via policy, on CPU for determinism
        model.eval()
        kit = S1Kit(model, bound=args.bound, device=str(device))
        policy = T3HaltingPolicy(s1=kit, eps=args.eps)

        m = exact_metrics_policy(policy, args.bound)
        fails = monotone_failure_cases(policy, args.bound)

        print(
            f"epoch={epoch} loss={loss.item():.4f} "
            f"coverage={m.coverage:.4f} acc_decided={m.accuracy_decided:.4f} "
            f"tpr={m.tpr:.4f} tnr={m.tnr:.4f} "
            f"tp={m.tp} tn={m.tn} fp={m.fp} fn={m.fn} "
            f"S2={m.source_counts.get('S2',0)} S1={m.source_counts.get('S1',0)} "
            f"monotone_failures={len(fails)}"
        )

    torch.save({"bound": args.bound, "state_dict": model.state_dict()}, args.save)
    print(f"saved: {args.save}")


if __name__ == "__main__":
    main()
