# train_bit_kit.py
from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Optional

from ml_bridge import generate_halting_dataset
from eval_ml import (
    build_kit_with_model,
    accuracy,
    monotone_mismatch_rate,
    monotone_detects_monotone_failure_rate,
    exact_metrics,
    monotone_failure_cases,
)

try:
    import torch
    import torch.nn as nn
except Exception:
    torch = None
    nn = None


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
    if torch is None:
        raise RuntimeError("PyTorch not available; install torch to run training")

    ap = argparse.ArgumentParser()
    ap.add_argument("--bound", type=int, default=10)
    ap.add_argument("--epochs", type=int, default=10)
    ap.add_argument("--batch", type=int, default=256)
    ap.add_argument("--hidden", type=int, default=64)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--device", type=str, default="cpu")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--save", type=str, default="bitkit.pt")
    args = ap.parse_args()

    torch.manual_seed(args.seed)
    device = torch.device(args.device)

    model = BitKitMLP(args.bound, hidden=args.hidden).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=args.lr)
    loss_fn = torch.nn.BCEWithLogitsLoss()

    # train
    model.train()
    steps_per_epoch = max(1, 4096 // args.batch)

    for epoch in range(1, args.epochs + 1):
        total_loss = 0.0
        for _ in range(steps_per_epoch):
            X, y = generate_halting_dataset(args.bound, args.batch, seed=None, device=args.device, p_monotone=0.5)
            
            # Inject the unique negative example every batch: all-zeros trace => Halts = 0
            X[0].zero_()
            y[0].zero_()

            opt.zero_grad(set_to_none=True)
            logits = model(X)
            loss = loss_fn(logits, y)
            loss.backward()
            opt.step()
            total_loss += float(loss.item())

        avg_loss = total_loss / steps_per_epoch

        # eval quick
        model.eval()
        K = build_kit_with_model(model, threshold=0.5)

        acc_mc = accuracy(K, args.bound, n_samples=2000, seed=args.seed + epoch)
        mmr_mc = monotone_mismatch_rate(K, args.bound, n_samples=2000, seed=args.seed + 100 + epoch)

        acc_exact, bacc_exact, tpr, tnr = exact_metrics(K, args.bound)
        mmr_exact = monotone_detects_monotone_failure_rate(K, args.bound)
        fails = monotone_failure_cases(K, args.bound)

        fail_str = ""
        if fails:
            # compact: list switchpoints that fail
            fail_str = " fails_sp=" + ",".join(str(f["sp"]) for f in fails)

        print(
            f"epoch={epoch} loss={avg_loss:.4f} "
            f"acc_mc={acc_mc:.4f} acc_exact={acc_exact:.4f} "
            f"bacc_exact={bacc_exact:.4f} tpr={tpr:.4f} tnr={tnr:.4f} "
            f"monotone_mismatch_mc={mmr_mc:.4f} monotone_mismatch_exact={mmr_exact:.4f}"
            f"{fail_str}"
        )
        model.train()

    # save
    torch.save(
        {"bound": args.bound, "state_dict": model.state_dict()},
        args.save,
    )
    print(f"saved: {args.save}")


if __name__ == "__main__":
    main()
