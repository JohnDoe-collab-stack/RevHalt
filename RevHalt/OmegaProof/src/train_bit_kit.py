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
    exact_metrics,
    monotone_failure_cases,
    exact_confusion,
    exact_confusion,
    fn_weight_histogram,
    exact_selective_metrics,
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
    ap.add_argument("--lambda_mono", type=float, default=1.0)
    ap.add_argument("--margin", type=float, default=5.0)
    ap.add_argument("--p_monotone", type=float, default=0.5)
    ap.add_argument("--mono_batch", type=int, default=None)
    ap.add_argument("--pos_weight", type=float, default=0.01)
    args = ap.parse_args()

    mono_batch = args.batch if args.mono_batch is None else args.mono_batch

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
            # Main mixed batch
            X, y = generate_halting_dataset(
                args.bound, args.batch, seed=None, device=args.device, p_monotone=args.p_monotone
            )
            
            # Inject the unique negative example every batch: all-zeros trace => Halts = 0
            X[0].zero_()
            y[0].zero_()

            logits = model(X)
            
            # Base loss
            loss_main = loss_fn(logits, y)

            # Positive Hinge Loss: Encourage positives to reduce False Negatives
            pos_mask = (y > 0.5).reshape(-1)
            if bool(pos_mask.any().item()):
                loss_pos = torch.relu(1.0 - logits[pos_mask]).mean()
            else:
                loss_pos = 0.0 * logits.mean()
            loss_pos = args.pos_weight * loss_pos

            # Monotone regularization batch (pure monotone)
            Xm, ym = generate_halting_dataset(
                args.bound, mono_batch, seed=None, device=args.device, p_monotone=1.0
            )

            logits_m = model(Xm)
            loss_mono = loss_fn(logits_m, ym)

            # Negative margin constraint on all-zeros (use the injected sample at index 0)
            logit_zero = logits[0, 0]
            loss_margin = torch.relu(logit_zero + args.margin)

            # Total loss
            loss = loss_main + args.lambda_mono * loss_mono + loss_margin + loss_pos

            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
            total_loss += float(loss.item())

        avg_loss = total_loss / steps_per_epoch

        # eval quick
        model.eval()
        K = build_kit_with_model(model, threshold=0.5)

        acc_exact, bacc_exact, tpr, tnr = exact_metrics(K, args.bound)
        fails = monotone_failure_cases(K, args.bound)
        fail_str = "none" if not fails else ",".join(str(f["sp"]) for f in fails)
        conf = exact_confusion(K, args.bound)

        print(
            f"epoch={epoch} loss={avg_loss:.4f} "
            f"acc_exact={acc_exact:.4f} tnr={tnr:.4f} tpr={tpr:.4f} "
            f"fails_sp={fail_str} "
            f"FN={conf['fn']} FP={conf['fp']}"
        )
        model.train()

    # Final diagnostic
    K_final = build_kit_with_model(model, threshold=0.5)
    conf = exact_confusion(K_final, args.bound)
    print(f"Final Exact Confusion: {conf}")

    hist = fn_weight_histogram(K_final, args.bound)
    print(f"FN Weight Histogram: {hist}")

    print("\n--- Selective Evaluation ---")
    for eps in [0.01, 0.05, 0.10]:
        sel = exact_selective_metrics(K_final, args.bound, epsilon=eps)
        print(f"eps={eps:.2f} coverage={sel['coverage']:.4f} acc_on_decided={sel['acc_on_covered']:.4f} FP={sel['fp']} FN={sel['fn']}")

    # save
    torch.save(
        {"bound": args.bound, "state_dict": model.state_dict()},
        args.save,
    )
    print(f"saved: {args.save}")


if __name__ == "__main__":
    main()
