"""
ml_witness.py — ML Witness Proposer Model

Input: Trace bits [bound]
Output: Logits [bound + 1]
    - Indices 0..bound-1: Confidence that index 'i' is limited (True).
    - Index bound: Confidence that NO witness exists (NOHALT / NULL).
"""

import torch
import torch.nn as nn

class WitnessModel(nn.Module):
    def __init__(self, bound: int, hidden: int = 64):
        super().__init__()
        self.bound = bound
        # Output size is bound + 1 (last one is NULL)
        self.net = nn.Sequential(
            nn.Linear(bound, hidden),
            nn.ReLU(),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
            nn.Linear(hidden, bound + 1)
        )

    def forward(self, x):
        return self.net(x)

    def predict_topk(self, x, k: int = 3):
        """
        Returns top-k indices from the distribution.
        """
        logits = self.forward(x)
        probs = torch.softmax(logits, dim=1)
        _, indices = torch.topk(probs, k, dim=1)
        return indices
