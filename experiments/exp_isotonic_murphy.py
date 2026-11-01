"""
Isotonic (CORP) Murphy decomposition beside the binned one, on Yeast.

Reuses the data split and the five classifiers of run_experiments.py (Experiment 4)
and computes, for every classifier and label, the binned terms (10 equal-width
bins, Proposition prop:murphy_binned) and the isotonic terms (aggmetrics.scores,
method='isotonic'). Writes data/exp5b_isotonic_murphy.csv and prints the checks quoted
in the paper.

Needs aggmetrics.scores (aggmetrics >= 0.3), or a checkout of the repository on the path:
    AGGMETRICS_SRC=/path/to/aggmetrics python exp_isotonic_murphy.py
"""
import os
import sys

import numpy as np
import pandas as pd
from scipy.stats import spearmanr

sys.path.insert(0, os.environ.get("AGGMETRICS_SRC", ""))
sys.path.insert(0, os.path.dirname(__file__))
import run_experiments as R                                     # noqa: E402
from aggmetrics.scores import ScoreMatrix, murphy                # noqa: E402


def main():
    X_tr, X_te, Y_tr, Y_te, labels = R.load_yeast()
    probas, _ = R.train_all(X_tr, X_te, Y_tr, Y_te)
    sm_y = {}
    rows = []
    for name, P in probas.items():
        sm = ScoreMatrix(Y_te, P, task="multilabel")
        sm_y[name] = sm
        b = murphy(sm, bins=10)
        iso = murphy(sm, method="isotonic")
        for j, lab in enumerate(labels):
            rows.append(dict(classifier=name, label=lab, BS=iso.brier[j],
                             UNC=iso.unc[j], REL_binned=b.rel[j], RES_binned=b.res[j],
                             REL_iso=iso.rel[j], RES_iso=iso.res[j]))
    df = pd.DataFrame(rows)
    R._save("exp5b_isotonic_murphy", df)

    # identity BS = UNC - RES + REL holds exactly for the isotonic terms
    err = np.abs(df.BS - (df.UNC - df.RES_iso + df.REL_iso)).max()
    print(f"max |BS - (UNC - RES + REL)| isotonic: {err:.1e}")

    g = df.groupby("classifier", sort=False)[["REL_binned", "REL_iso",
                                              "RES_binned", "RES_iso"]].mean()
    print(g.round(4))
    for t in ("REL", "RES"):
        rho = [spearmanr(d[f"{t}_binned"], d[f"{t}_iso"])[0]
               for _, d in df.groupby("classifier")]
        print(f"Spearman binned vs isotonic {t} over labels: "
              f"{min(rho):.2f}-{max(rho):.2f}")
    piv = {t: df.pivot(index="label", columns="classifier", values=t)
           for t in ("REL_binned", "REL_iso", "RES_binned", "RES_iso")}
    for v in ("binned", "iso"):
        rel, res = piv[f"REL_{v}"], piv[f"RES_{v}"]
        print(f"[{v}] MLP(cal) REL < MLP(uncal) on "
              f"{int((rel['MLP (cal.)'] < rel['MLP (uncal.)']).sum())}/14; "
              f"GBT RES > LR on {int((res['GBT'] > res['LR']).sum())}/14; "
              f"RF RES > LR on {int((res['RF'] > res['LR']).sum())}/14")
    unc = df.groupby("label").UNC.first()
    for v in ("binned", "iso"):
        r = [spearmanr(unc.reindex(d.label), d[f"RES_{v}"])[0]
             for _, d in df.groupby("classifier")]
        s = [spearmanr(unc.reindex(d.label), d[f"REL_{v}"])[0]
             for _, d in df.groupby("classifier")]
        print(f"[{v}] Spearman RES~UNC {min(r):.2f}-{max(r):.2f}; "
              f"REL~UNC {min(s):.2f}-{max(s):.2f}")
    # cross term of the isotonic REL
    ratios = []
    for name, sm in sm_y.items():
        iso = murphy(sm, method="isotonic")
        ratios.append(iso.rel.mean())
    print("mean isotonic REL by classifier:", np.round(ratios, 4))


if __name__ == "__main__":
    main()
