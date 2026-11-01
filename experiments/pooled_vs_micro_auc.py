"""
Weighted micro-AUC (Equation eq:auc_micro) versus globally pooled ROC-AUC
(Remark 80): a seeded synthetic computation, replacing the unscripted 0.038
of the working manuscript.

Generator (one draw): n = 200 examples, m = 5 classes, binary relevance.
  - prevalences pi_j ~ U(0.15, 0.50), labels Y_ij ~ Bernoulli(pi_j), independent;
  - latent score z_ij = d * Y_ij + N(0, 1), with separation d = 1.5;
  - per-class output scale: Yhat_ij = sigmoid(a_j * z_ij + b_j), with
    a_j ~ U(0.5, 2.0) and b_j ~ U(-2.0, 2.0) drawn independently per class
    ("different scales"), or a_j = 1, b_j = 0 for every class ("common scale").
A monotone per-class map leaves every AUC_j, hence the weighted micro-AUC,
unchanged; only the pooled ROC-AUC compares cells across classes.

Writes data/pooled_vs_micro_auc.csv (one row per draw and scenario) and prints
the summary quoted in Remark 80.
"""
import os

import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

from metrics import auc_micro

SEED = 42
N, M, D, R = 200, 5, 1.5, 1000
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def draw(rng, common_scale):
    pi = rng.uniform(0.15, 0.50, size=M)
    Y = (rng.random((N, M)) < pi).astype(int)
    while (Y.sum(axis=0) == 0).any() or (Y.sum(axis=0) == N).any():
        Y = (rng.random((N, M)) < pi).astype(int)
    z = D * Y + rng.standard_normal((N, M))
    if common_scale:
        a, b = np.ones(M), np.zeros(M)
    else:
        a, b = rng.uniform(0.5, 2.0, size=M), rng.uniform(-2.0, 2.0, size=M)
    Yhat = 1.0 / (1.0 + np.exp(-(a * z + b)))
    micro = auc_micro(Y, Yhat)
    pooled = float(roc_auc_score(Y.ravel(), Yhat.ravel()))
    return micro, pooled


def main():
    rng = np.random.default_rng(SEED)
    rows = []
    for scenario, common in [("different_scales", False), ("common_scale", True)]:
        for r in range(R):
            micro, pooled = draw(rng, common)
            rows.append({"scenario": scenario, "draw": r, "micro_auc": micro,
                         "pooled_auc": pooled, "gap": micro - pooled})
    df = pd.DataFrame(rows)
    os.makedirs(DATA_DIR, exist_ok=True)
    df.to_csv(os.path.join(DATA_DIR, "pooled_vs_micro_auc.csv"), index=False)
    for scenario, g in df.groupby("scenario", sort=False):
        gap = g["gap"].to_numpy()
        print(f"{scenario:17s} draws={len(gap)}  mean gap={gap.mean():+.4f}  "
              f"sd={gap.std(ddof=1):.4f}  mean |gap|={np.abs(gap).mean():.4f}  "
              f"median |gap|={np.median(np.abs(gap)):.4f}  "
              f"5-95% |gap|=({np.quantile(np.abs(gap), 0.05):.4f}, "
              f"{np.quantile(np.abs(gap), 0.95):.4f})")


if __name__ == "__main__":
    main()
